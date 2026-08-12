module Main (main) where

import TypeTheory
import Data.Maybe

-- The following is a partial implementation of the formal type theory defined in appendix A.2 in the HoTT book.
-- HoTT book: https://hott.github.io/book/hott-online-82-g578b85c.pdf

universe :: Type
universe = Type { typeSize = 1, typeId = 0 }

universeMinusOne :: Term
universeMinusOne = Constant 0

universeMinusOneOut :: TermOut
universeMinusOneOut = ConstantOut 0

universe0Out :: TermOut
universe0Out = universeNextOut universeMinusOneOut

universeNext :: Term -> Term
universeNext x = Instance { typeOf = universe, instanceTerms = [x] }

universeNextOut :: TermOut -> TermOut
universeNextOut x = InstanceOut { typeOfTerm = universe, termParts = [x] }

universeTerm :: Int -> Term
universeTerm = universeNext . Generic

universeTermOut :: Int -> TermOut
universeTermOut = universeNextOut . GenericOut

universeAssumption :: Int -> Int -> JudgementIn
universeAssumption x y = Membership [] (Generic x) (universeTerm y)

universe_BASE :: Rule
universe_BASE = Rule { assumptions = [], conclusion = Membership [] (universeMinusOneOut) (universe0Out) }

universe_INTRO :: Rule
universe_INTRO = Rule
  { assumptions = [universeAssumption 0 1]
  , conclusion = Membership [] (universeNextOut $ GenericOut 1) (universeNextOut $ universeNextOut $ GenericOut 1) }

ctx_EMP :: Rule
ctx_EMP = Rule { assumptions = [], conclusion = Ctx [] }

ctx_EXT :: Rule
ctx_EXT = Rule
  { assumptions = [ Membership [SubContextIn 0] (Generic 0) (universeTerm 1) ]
  , conclusion = Ctx [SubContextOut 0, NewGeneric $ GenericOut 0]
  }

vble :: Rule
vble = Rule
  { assumptions = [Ctx [SubContextIn 1, SubContextIn 0]]
  , conclusion = Membership [SubContextOut 1, SubContextOut 0] (SubContextHeadGeneric 1) (SubContextHeadTerm 1) }

pointType :: Type
pointType = Type { typeSize = 0, typeId = 1 }

pointOut :: TermOut
pointOut = InstanceOut { typeOfTerm = pointType, termParts = [] }

point :: Term
point = Instance { typeOf = pointType, instanceTerms = [] }

pointElementOut :: TermOut
pointElementOut = ConstantOut 1

pointElement :: Term
pointElement = Constant 1

-- point_INTRO :: Rule
-- point_INTRO = Rule
--   { assumptions = [Ctx [SubContextIn 0]]
--   , conclusion = Membership [SubContextOut 0] pointElementOut pointOut}

point_FORM :: Rule
point_FORM = Rule
  { assumptions = [Ctx [SubContextIn 0], universeAssumption 0 1]
  , conclusion = Membership [SubContextOut 0] pointOut (universeTermOut 1)}


dependantType :: Type
dependantType = Type { typeSize = 2, typeId = 2 }

dependantOut :: Int -> TermOut -> TermOut -> TermOut
dependantOut x a b = InstanceConsume {typeOfTerm = dependantType, termParts = [a, b], consumeId = x}

functionType :: Type
functionType = Type { typeSize = 2, typeId = 3 }

functionOut :: Int -> TermOut -> TermOut -> TermOut
functionOut x a b = InstanceConsume {typeOfTerm = functionType, termParts = [a, b], consumeId = x}

dependant_INTRO :: Rule
dependant_INTRO = Rule
  { assumptions = [ Membership [SubContextIn 0, OfTypeIn 0 (Generic 1)] (Generic 2) (Generic 3)]
  , conclusion = Membership
    [SubContextOut 0]
    (functionOut 0 (GenericOut 1) (GenericOut 2))
    (dependantOut 0 (GenericOut 1) (GenericOut 3)) }

-- subst1 :: Rule
-- subst1 = Rule
--   { assumptions =
--     [ Membership [SubContextIn 0] (Generic 0) (Generic 1)
--     , Membership [SubContextIn 0, OfTypeIn (2, Generic 1), SubContextIn 1] (Generic 3) (Generic 4)
--     ]
--   , conclusion = Membership [SubContextOut 0, SubContextReplace (1, GenericOut 0, 2)]
--       (GenericReplace (3, GenericOut 0, 2)) (GenericReplace (4, GenericOut 0, 2))
--   }

-- eqReflex :: Rule
-- eqReflex = Rule
--   { assumptions = [Membership [SubContextIn 0] (Generic 0) (Generic 1)]
--   , conclusion = DefEq [SubContextOut 0] (GenericOut 0) (GenericOut 0) (GenericOut 1)
--   }

-- The following is an test of the derivation found on page 434 in the HoTT book.

emptyCtx :: Judgement
emptyCtx = fromJust $ apply ctx_EMP [] []

universeMinusOneJudgement :: Judgement
universeMinusOneJudgement = fromJust $ apply universe_BASE [] []

universe0Judgement :: Judgement
universe0Judgement = fromJust $ apply universe_INTRO [] [universeMinusOneJudgement]

pointJudgement :: Judgement
pointJudgement = fromJust $ apply point_FORM [] [emptyCtx, universe0Judgement]

pointVariableCtx :: Judgement
pointVariableCtx = fromJust $ apply ctx_EXT [] [pointJudgement]

pointVariableJudgement :: Judgement -- TODO this does not work. Debug
pointVariableJudgement = fromJust $ apply vble [0] [pointVariableCtx]

pointIdFunctionJudgement :: Judgement
pointIdFunctionJudgement = fromJust $ apply dependant_INTRO [] [pointVariableJudgement]

main :: IO ()
main = putStrLn $ if pointVariableCtx == Ctx [point] then "Good" else "Bad"

-- TODO tests
-- apply emptyCtx == Ctx []

-- TODO call Types for Constructs

-- TODO error instead of Maybe
