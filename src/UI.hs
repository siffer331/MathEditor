{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module UI (startUI) where

import TypeTheory
import TypeTheoryExamples
import Control.Lens
import Data.Maybe
import Data.List
import Data.Text (Text)
import Monomer
import TextShow
import Colors
import UIData
import Util

type AppNode = WidgetNode AppModel AppEvent
type AppEnv = WidgetEnv AppModel AppEvent

focusKeys :: [(Text, AppEvent)]
focusKeys = (\(a, b) -> (a, AppMoveFocus b)) <$>
  [ ("Enter", FocusEnter)
  , ("Space", FocusEnter)
  , ("Esc", FocusExit)
  , ("h", FocusLeft)
  , ("Left", FocusLeft)
  , ("j", FocusDown)
  , ("Down", FocusDown)
  , ("k", FocusUp)
  , ("Up", FocusUp)
  , ("l", FocusRight)
  , ("Right", FocusRight)
  ]

buildUI :: AppEnv -> AppModel -> AppNode
buildUI _ model = widgetTree where
  widgetTree = keystroke focusKeys $ vstack
    [ filler
    , hstack
      [ filler
      , displayRule (model ^. appRuleVisual) $ model ^. appSelection
      , filler
      ]
    , filler
    ] `styleBasic` [bgColor colorBase, textSize 24]

handleEvent
  :: WidgetEnv AppModel AppEvent
  -> WidgetNode AppModel AppEvent
  -> AppModel
  -> AppEvent
  -> [AppEventResponse AppModel AppEvent]
handleEvent _ _ model evt = case evt of
  AppInit -> []
  AppMoveFocus move -> [Model $ over appSelection (moveFocusRule (visualRule $ model ^. appRuleVisual) move) model ]
  -- AppIncrease -> [Model (model & clickCount +~ 1)]

startUI :: IO ()
startUI = do
  startApp model handleEvent buildUI config
  where
    config = [
      appWindowTitle "Hello world",
      appWindowIcon "./assets/images/icon.png",
      appTheme darkTheme,
      appFontDef "Regular" "./assets/fonts/lmmath-regular.otf",
      appInitEvent AppInit
      ]
    model = AppModel SelectionWhole visual_subst1

styleSelect :: Bool -> StyleState
styleSelect x = styleIf x $ bgColor colorSurface1

displayRule :: RuleVisual -> Selection RuleSelection -> AppNode
displayRule visual selection = hstack
  [ vstack
    [ (flip styleBasic [paddingH 10, paddingV 5]) $
      hstack (intersperse (spacer_ [width 30]) $ 
        (\i judgement -> displayJudgement (displayContextPartIn visual) (displayTerm visual) judgement
          `styleBasic` [styleSelect $ selection == SelectionSub (SelectionAssumption i SelectionWhole)])
        <||> assumptions (visualRule visual))
    , separatorLine
    , (flip styleBasic [paddingH 10, paddingV 5, styleSelect $ selection == SelectionSub (SelectionConclusion SelectionWhole)]) $
      displayJudgement (displayContextPartOut visual) (displayTermOut visual) $ conclusion $ visualRule visual
    ]
  , spacer
  , label (visualName visual) `styleBasic` [textCenter]
  ] `styleBasic` [padding 5, styleSelect $ selection == SelectionWhole]

displayJudgement :: (ctx -> AppNode) -> (term -> AppNode) -> JudgementType [ctx] term -> AppNode
displayJudgement ctxF _ (Ctx ctx) = hstack [displayContext ctxF ctx, label " ctx" ]
displayJudgement ctxF termF (Membership ctx term termType)
  = hstack [ displayContext ctxF ctx, label " ⊢ ", termF term, label " : ", termF termType ]
displayJudgement ctxF termF (DefEq ctx termA termB termType)
  = hstack [ displayContext ctxF ctx, label " ⊢ ", termF termA, label " ≡ ", termF termB, label " : ", termF termType ]

displayContext :: (ctxPart -> AppNode) -> [ctxPart] -> AppNode
displayContext _ [] = label "·"
displayContext f ctxParts = hstack $ intersperse (label ", ") $ f <$> ctxParts

displayContextPartIn :: RuleVisual -> ContextPartIn -> AppNode
displayContextPartIn visual (SubContextIn x) = getSubContextLabel visual x
displayContextPartIn visual (OfTypeIn x term) = hstack
  [ getGenericLabel visual x
  , label ":" , displayTerm visual term
  ]

displayContextPartOut :: RuleVisual -> ContextPartOut -> AppNode
displayContextPartOut visual (NewGeneric term)
  = hstack
    [ getSubContextLabel visual (-1) -- TODO using -1 is a bit stupid but works for now
    , label " : "
    , displayTermOut visual term
    ]
displayContextPartOut visual (SubContextOut x) = getSubContextLabel visual x
displayContextPartOut visual (SubContextReplace {contextId = x, ctxReplacingTerm = term, ctxReplacedId = y})
  = hstack
    [ getSubContextLabel visual x
    , label "["
    , displayTermOut visual term
    , label "/"
    , getGenericLabel visual y
    , label "]"
    ]

displayTerm :: RuleVisual -> Term -> AppNode
displayTerm visual (Generic x) = getGenericLabel visual x
displayTerm visual (Instance {typeOf = termType, instanceTerms = terms} ) = hstack $ concat -- TODO
  [ [label "("]
  , intersperse (label ", ") $ displayTerm visual <$> terms
  , [label $ " : " <> (showt $ typeId termType) <> ")"]
  ]
displayTerm _ (Constant x) = label $ "Const " <> showt x
displayTerm _ (Internal x) = label $ "Internal " <> showt x

displayTermOut :: RuleVisual -> TermOut -> AppNode
displayTermOut visual (GenericOut x) = getGenericLabel visual x
displayTermOut visual (InstanceOut {typeOfTerm = termType, termParts = terms} ) = hstack $ concat -- TODO
  [ [label "("]
  , intersperse (label ", ") $ displayTermOut visual <$> terms
  , [label $ " : " <> (showt $ typeId termType) <> ")"]
  ]
displayTermOut visual (InstanceConsume {typeOfTerm = termType, termParts = terms} ) = hstack $ concat -- TODO
  [ [label "("]
  , intersperse (label ", ") $ displayTermOut visual <$> terms
  , [label $ " : " <> (showt $ typeId termType) <> ")"]
  ]
displayTermOut visual (GenericReplace {genericId = x, termReplacingTerm = term, termReplacedId = y})
  = hstack
    [ getGenericLabel visual x
    , label "["
    , displayTermOut visual term
    , label "/"
    , getGenericLabel visual y
    , label "]"
    ]
displayTermOut _ (ConstantOut x) = label $ "Const " <> showt x
displayTermOut visual (SubContextHeadTerm x) = hstack
  [ label $ (displayToken x $ visualSubContextSymbols visual)
  , label "[T]"
  ]
displayTermOut visual (SubContextHeadGeneric x) = hstack
  [ label $ (displayToken x $ visualSubContextSymbols visual)
  , label "[t]"
  ]

_visual_ctx_EMP :: RuleVisual
_visual_ctx_EMP = RuleVisual
  { visualRule = ctx_EMP
  , visualGenericSymbols = []
  , visualSubContextSymbols = []
  , visualName = "ctx-EMP" }

visual_subst1 :: RuleVisual
visual_subst1 = RuleVisual
  { visualRule = subst1
  , visualGenericSymbols = [(0, "a"), (1, "A"), (2, "x"), (3, "b"), (4, "B")]
  , visualSubContextSymbols = [(0, "Γ"), (1, "∆")]
  , visualName = "Subst1" }

_visual_eqReflex :: RuleVisual
_visual_eqReflex = RuleVisual
  { visualRule = eqReflex
  , visualGenericSymbols = [(0, "a"), (1, "A")]
  , visualSubContextSymbols = [(0, "Γ")]
  , visualName = "Eq Reflexive" }

getGenericLabel :: RuleVisual -> Int -> AppNode
getGenericLabel visual x = label $ displayToken x $ visualGenericSymbols visual

getSubContextLabel :: RuleVisual -> Int -> AppNode
getSubContextLabel visual x = label $ displayToken x $ visualSubContextSymbols visual

displayToken :: Int -> [(Int, Text)] -> Text
displayToken x = fromMaybe (showt x) . lookup x

moveFocusRule :: Rule -> MoveFocus -> Selection RuleSelection -> Selection RuleSelection
moveFocusRule _ FocusEnter SelectionWhole = SelectionSub $ SelectionAssumption 0 SelectionWhole
moveFocusRule _ FocusExit (SelectionSub (SelectionAssumption _ SelectionWhole)) = SelectionWhole
moveFocusRule _ FocusLeft (SelectionSub (SelectionAssumption x SelectionWhole))
  = SelectionSub $ SelectionAssumption (max 0 $ x - 1) SelectionWhole
moveFocusRule rule FocusRight (SelectionSub (SelectionAssumption x SelectionWhole))
  = SelectionSub $ SelectionAssumption (min (length (assumptions rule) - 1) $ x + 1) SelectionWhole
moveFocusRule _ FocusExit (SelectionSub (SelectionConclusion SelectionWhole)) = SelectionWhole
moveFocusRule _ FocusDown (SelectionSub (SelectionAssumption _ SelectionWhole))
  = SelectionSub $ SelectionConclusion SelectionWhole
moveFocusRule _ FocusUp (SelectionSub (SelectionConclusion SelectionWhole))
  = SelectionSub $ SelectionAssumption 0 SelectionWhole
moveFocusRule _ FocusEnter (SelectionSub (SelectionAssumption x SelectionWhole))
  = SelectionSub $ SelectionAssumption x $ SelectionSub $ SelectionCtx SelectionWhole
moveFocusRule _ FocusEnter (SelectionSub (SelectionConclusion SelectionWhole))
  = SelectionSub $ SelectionConclusion $ SelectionSub $ SelectionCtx SelectionWhole
moveFocusRule _ _ selection = selection

moveFocusJudgement :: Judgement -> MoveFocus -> Selection (JudgementSelection a b) -> Selection (JudgementSelection a b)
moveFocusJudgement = undefined






