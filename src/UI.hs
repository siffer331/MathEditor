{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module UI (startUI) where

import TypeTheory
import TypeTheoryExamples
import Control.Lens
import Data.Maybe
import Data.List
import Data.Text (Text, pack)
import Monomer
import TextShow

import qualified Monomer.Lens as L

newtype AppModel = AppModel
  { _clickCount :: Int
  } deriving (Eq, Show)

data AppEvent
  = AppInit
  | AppIncrease
  deriving (Eq, Show)

makeLenses 'AppModel

type AppNode = WidgetNode AppModel AppEvent
type AppEnv = WidgetEnv AppModel AppEvent

buildUI :: AppEnv -> AppModel -> AppNode
buildUI _ _ = widgetTree where
  widgetTree = vstack
    [ filler
    , hstack
      [ filler
      , displayRule visual_subst1
      , filler
      ]
    , filler
    ] `styleBasic` [bgColor $ rgbHex "#1e1e2e", textSize 24]

handleEvent
  :: WidgetEnv AppModel AppEvent
  -> WidgetNode AppModel AppEvent
  -> AppModel
  -> AppEvent
  -> [AppEventResponse AppModel AppEvent]
handleEvent _ _ model evt = case evt of
  AppInit -> []
  AppIncrease -> [Model (model & clickCount +~ 1)]

startUI :: IO ()
startUI = do
  startApp model handleEvent buildUI config
  where
    config = [
      appWindowTitle "Hello world",
      appWindowIcon "./assets/images/icon.png",
      appTheme darkTheme,
      appFontDef "Regular" "./assets/fonts/lmmath-regular.otf",
      -- appFontDef "Regular" "./assets/fonts/Roboto-Regular.ttf",
      appInitEvent AppInit
      ]
    model = AppModel 0

displayRule :: RuleVisual -> AppNode
displayRule visual = hstack
  [ vstack
    [ (`styleBasic` [paddingH 10, paddingV 5]) $
      hstack $ intersperse (spacer_ [width 30]) $ displayJudgement (displayContextPartIn visual) (displayTerm visual)
        <$> assumptions (visualRule visual)
    , separatorLine
    , (`styleBasic` [paddingH 10, paddingV 5]) $
      displayJudgement (displayContextPartOut visual) (displayTermOut visual) $ conclusion $ visualRule visual
    ]
  , spacer
  , label (visualName visual) `styleBasic` [textCenter]
  ]

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
  , [label $ pack $ " : " ++ (show $ typeId termType) ++ ")"]
  ]
displayTerm _ (Constant x) = label $ pack $ "Const " ++ show x
displayTerm _ (Internal x) = label $ pack $ "Internal " ++ show x

displayTermOut :: RuleVisual -> TermOut -> AppNode
displayTermOut visual (GenericOut x) = getGenericLabel visual x
displayTermOut visual (InstanceOut {typeOfTerm = termType, termParts = terms} ) = hstack $ concat -- TODO
  [ [label "("]
  , intersperse (label ", ") $ displayTermOut visual <$> terms
  , [label $ pack $ " : " ++ (show $ typeId termType) ++ ")"]
  ]
displayTermOut visual (InstanceConsume {typeOfTerm = termType, termParts = terms} ) = hstack $ concat -- TODO
  [ [label "("]
  , intersperse (label ", ") $ displayTermOut visual <$> terms
  , [label $ pack $ " : " ++ (show $ typeId termType) ++ ")"]
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
displayTermOut _ (ConstantOut x) = label $ pack $ "Const " ++ show x
displayTermOut visual (SubContextHeadTerm x) = hstack
  [ label $ (displayToken x $ visualSubContextSymbols visual)
  , label "[T]"
  ]
displayTermOut visual (SubContextHeadGeneric x) = hstack
  [ label $ (displayToken x $ visualSubContextSymbols visual)
  , label "[t]"
  ]

visual_ctx_EMP :: RuleVisual
visual_ctx_EMP = RuleVisual
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

visual_eqReflex :: RuleVisual
visual_eqReflex = RuleVisual
  { visualRule = eqReflex
  , visualGenericSymbols = [(0, "a"), (1, "A")]
  , visualSubContextSymbols = [(0, "Γ")]
  , visualName = "Eq Reflexive" }

data RuleVisual = RuleVisual
  { visualRule :: Rule
  , visualGenericSymbols :: [(Int, Text)]
  , visualSubContextSymbols :: [(Int, Text)]
  , visualName :: Text }

getGenericLabel :: RuleVisual -> Int -> AppNode
getGenericLabel visual x = label $ displayToken x $ visualGenericSymbols visual

getSubContextLabel :: RuleVisual -> Int -> AppNode
getSubContextLabel visual x = label $ displayToken x $ visualSubContextSymbols visual

displayToken :: Int -> [(Int, Text)] -> Text
displayToken x = fromMaybe (pack $ show x) . lookup x


data JudgementSelection = SelectionAssumption Int | SelectionConclusion
