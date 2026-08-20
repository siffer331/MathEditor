{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module UIData where

import TypeTheory
import Control.Lens
import Data.Text (Text)
import Data.Maybe

data AppModel = AppModel
  { _appSelection :: Selection
  , _appRuleVisual :: RuleVisual
  } deriving (Eq, Show)

-- type IsEditing = Bool

-- data Selection x = SelectionNone | SelectionWhole | SelectionSub x deriving (Eq, Show)

-- data RuleSelection
--   = SelectionAssumption Int (Selection (JudgementSelection CtxPartInSelection TermOutSelection))
--   | SelectionConclusion (Selection (JudgementSelection CtxPartOutSelection TermOutSelection))
--   | SelectionRuleName IsEditing
--   deriving (Eq, Show)

-- data JudgementSelection ctxPartSelect termSelect
--   = SelectionCtx (Selection (Int, Selection ctxPartSelect))
--   | SelectionJudgementTermA (Selection termSelect)
--   | SelectionJudgementTermB (Selection termSelect)
--   | SelectionJudgementType (Selection termSelect)
--   deriving (Eq, Show)

-- data CtxPartInSelection
--   = SelectionSubContext IsEditing
--   | SelectionCtxTerm IsEditing
--   | SelectionCtxType (Selection TermSelection)
--   deriving (Eq, Show)
-- data CtxPartOutSelection
--   = SelectionOutSubContext IsEditing
--   | SelectionNewTerm IsEditing
--   | SelectionNewType (Selection TermOutSelection)
--   | SelectionCtxReplaceTerm (Selection TermOutSelection)
--   | SelectionCtxReplaceGeneric IsEditing
--   deriving (Eq, Show)
-- data TermSelection = SelectionTermSimple IsEditing | SelectionInstance Int (Selection TermSelection)
--   deriving (Eq, Show)
-- data TermOutSelection
--   = SelectionTermOutSimble IsEditing
--   | SelectionInstanceOut Int (Selection TermOutSelection)
--   | SelectionInstanceInput IsEditing
--   | SelectionTermReplaceing (Selection TermOutSelection)
--   | SelectionTermReplaceGeneric IsEditing
--   deriving (Eq, Show)

data MoveFocus = FocusEnter | FocusExit | FocusLeft | FocusRight | FocusUp | FocusDown deriving (Eq, Show)

data AppEvent
  = AppInit
  | AppMoveFocus MoveFocus
  deriving (Eq, Show)

data RuleVisual = RuleVisual
  { visualRule :: Rule
  , visualGenericSymbols :: [(Int, Text)]
  , visualSubContextSymbols :: [(Int, Text)]
  , visualName :: Text } deriving (Eq, Show)

data SelectionDir = SelectVertical [SelectionContainer] | SelectHorizontal [SelectionContainer] deriving (Eq, Show)
data SelectionContainer = SelectionEnd | SelectionParts Int SelectionContainer | SelectionNext SelectionDir deriving (Eq, Show)

data Selection = SelectionWhole | SelectionSub Int Selection deriving (Eq, Show)

getSelectionContainer :: Int -> SelectionDir -> SelectionContainer
getSelectionContainer x (SelectVertical xs) = xs !! x
getSelectionContainer x (SelectHorizontal xs) = xs !! x

moveSelection :: SelectionDir -> MoveFocus -> Selection -> Selection
moveSelection dir move selection = fromMaybe selection $ moveSelection' dir move selection

moveSelection' :: SelectionDir -> MoveFocus -> Selection -> Maybe Selection
moveSelection' (SelectHorizontal _) FocusLeft (SelectionSub x (SelectionWhole))
  | x == 0    = Just $ SelectionSub x SelectionWhole
  | otherwise = Just $ SelectionSub (x - 1) SelectionWhole
moveSelection' (SelectHorizontal containers) FocusRight (SelectionSub x (SelectionWhole))
  | x == length containers - 1 = Just $ SelectionSub x SelectionWhole
  | otherwise                  = Just $ SelectionSub (x + 1) SelectionWhole
moveSelection' (SelectVertical _) FocusUp (SelectionSub x (SelectionWhole))
  | x == 0    = Just $ SelectionSub x SelectionWhole
  | otherwise = Just $ SelectionSub (x - 1) SelectionWhole
moveSelection' (SelectVertical containers) FocusDown (SelectionSub x (SelectionWhole))
  | x == length containers - 1 = Just $ SelectionSub x SelectionWhole
  | otherwise                  = Just $ SelectionSub (x + 1) SelectionWhole
moveSelection' _ FocusEnter SelectionWhole = Just $ SelectionSub 0 SelectionWhole
moveSelection' containers FocusEnter (SelectionSub x sub) = SelectionSub x <$>
  moveSelectionContainer (getSelectionContainer x containers) FocusEnter sub
moveSelection' _ FocusExit SelectionWhole = Nothing
moveSelection' containers FocusExit (SelectionSub x sub) =
  let newSub = moveSelectionContainer (getSelectionContainer x containers) FocusExit sub in
    if newSub /= Nothing then SelectionSub x <$> newSub else Just SelectionWhole
moveSelection' _ _ SelectionWhole = Nothing
moveSelection' (SelectHorizontal containers) dir (SelectionSub x sub)
  | newSub /= Nothing = SelectionSub x <$> newSub
  | newSub == Nothing && dir == FocusLeft && x == 0 = Just $ SelectionSub x sub
  | newSub == Nothing && dir == FocusLeft = Just $ SelectionSub (x - 1) sub
  | newSub == Nothing && dir == FocusRight && x == length containers - 1 = Just $ SelectionSub x sub
  | newSub == Nothing && dir == FocusRight = Just $ SelectionSub (x + 1) sub
  | otherwise = Just $ SelectionSub x sub
  -- | otherwise = Nothing
  where newSub = moveSelectionContainer (containers !! x) dir sub
moveSelection' (SelectVertical containers) dir (SelectionSub x sub)
  | newSub /= Nothing = SelectionSub x <$> newSub
  | newSub == Nothing && dir == FocusUp && x == 0 = Just $ SelectionSub x sub
  | newSub == Nothing && dir == FocusUp = Just $ SelectionSub (x - 1) sub
  | newSub == Nothing && dir == FocusDown && x == length containers - 1 = Just $ SelectionSub x sub
  | newSub == Nothing && dir == FocusDown = Just $ SelectionSub (x + 1) sub
  | otherwise = Just $ SelectionSub x sub
  -- | otherwise = Nothing
  where newSub = moveSelectionContainer (containers !! x) dir sub

moveSelectionContainer :: SelectionContainer -> MoveFocus -> Selection -> Maybe Selection
moveSelectionContainer SelectionEnd _ _ = Nothing
moveSelectionContainer (SelectionParts _ container) FocusEnter (SelectionSub x sub) =
  SelectionSub x <$> moveSelectionContainer container FocusEnter sub
moveSelectionContainer (SelectionNext containers) FocusEnter (SelectionSub x sub) =
  SelectionSub x <$> moveSelection' containers FocusEnter sub
moveSelectionContainer _ FocusEnter SelectionWhole = Just $ SelectionSub 0 SelectionWhole
moveSelectionContainer _ FocusExit SelectionWhole = Nothing
moveSelectionContainer (SelectionParts _ container) FocusExit (SelectionSub x sub) =
  let newSub = moveSelectionContainer container FocusExit sub in
    if newSub /= Nothing then SelectionSub x <$> newSub else Just SelectionWhole
moveSelectionContainer (SelectionNext containers) FocusExit (SelectionSub x sub) =
  let newSub = moveSelection' containers FocusExit sub in
    if newSub /= Nothing then SelectionSub x <$> newSub else Just SelectionWhole
-- FocusExit and FocusEnter are handled so only directions remain
moveSelectionContainer _ _ SelectionWhole = Nothing
moveSelectionContainer (SelectionNext containers) dir selection = moveSelection' containers dir selection
moveSelectionContainer (SelectionParts l _) dir (SelectionSub x SelectionWhole)
  | (dir == FocusLeft || dir == FocusUp) && x == 0 = Nothing
  | (dir == FocusLeft || dir == FocusUp) = Just $ SelectionSub (x - 1) SelectionWhole
  | (dir == FocusRight || dir == FocusDown) && x == l - 1 = Nothing
  | (dir == FocusRight || dir == FocusDown) = Just $ SelectionSub (x - 1) SelectionWhole
moveSelectionContainer (SelectionParts _ container) dir (SelectionSub x sub) =
  SelectionSub x <$> moveSelectionContainer container dir sub

makeLenses ''AppModel
