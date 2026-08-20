module TypeTheory
  ( Term (..)
  , Judgement
  , JudgementIn
  , JudgementOut
  , JudgementType (..)
  , Type (..)
  , Rule (..)
  , Context
  , ContextPartIn (..)
  , ContextPartOut (..)
  , ContextIn
  , ContextOut
  , TermOut (..)
  , Error (..)
  , Result
  , apply
  ) where

import Control.Monad
import Util

data Type = Type { typeSize :: Int, typeId :: Int } deriving Show

instance Eq Type where
  x == y = typeId x == typeId y

--            context index
data Term = Generic Int | Instance {typeOf :: Type, instanceTerms :: [Term]} | Constant Int | Internal Int deriving (Eq, Show)

type Context = [Term]

--           Context is good | Context implies Term is of type Term | Context implies that Term and Term are equal of type Term
data JudgementType ctx term = Ctx ctx | Membership ctx term term | DefEq ctx term term term deriving (Eq, Show)

type Judgement = JudgementType Context Term

data TermOut
  = GenericOut Int
  | InstanceOut {typeOfTerm :: Type, termParts :: [TermOut]}
  | InstanceConsume {typeOfTerm :: Type, termParts :: [TermOut], consumeId :: Int}
  | GenericReplace {genericId :: Int, termReplacingTerm :: TermOut, termReplacedId :: Int}
  | ConstantOut Int
  | SubContextHeadTerm Int
  | SubContextHeadGeneric Int
  deriving (Show, Eq)

data ContextPartIn = OfTypeIn Int Term | SubContextIn Int deriving (Show, Eq)

data ContextPartOut
  = NewGeneric TermOut
  | SubContextOut Int
  | SubContextReplace {contextId :: Int, ctxReplacingTerm :: TermOut, ctxReplacedId :: Int}
  deriving (Show, Eq)

type ContextIn = [ContextPartIn]
type ContextOut = [ContextPartOut]

type JudgementIn = JudgementType ContextIn Term
type JudgementOut = JudgementType ContextOut TermOut

data Rule = Rule {assumptions :: [JudgementIn], conclusion :: JudgementOut} deriving (Show, Eq)

apply :: Rule -> [(Int, Int)] -> [Judgement] -> Result Judgement
apply rule lengths contexts = do
  termLookup <- collectJudgements lengths (assumptions rule) contexts
  createJudgement termLookup $ conclusion rule

type TermLookup = ([(Int, (Int, Context))], [(Int, Term)])

emptyLookup :: TermLookup
emptyLookup = ([], [])

mergeTermLookup :: TermLookup -> Result TermLookup
mergeTermLookup (a, b) = do
  mergedA <- mergeLookup (\x y z -> ConflictingSubContexts x (snd y) (snd z)) a
  mergedB <- mergeLookup ConflictingTerms b
  return (mergedA, mergedB)

mergeLookup :: (Eq a, Eq b) => (a -> b -> b -> Error) -> [(a, b)] -> Result [(a, b)]
mergeLookup f = foldl (\a b -> join $ (flip (insertLookup f) <$> a) ?? b) $ Right []

insertLookup :: (Eq a, Eq b) => (a -> b -> b -> Error) -> (a, b) -> [(a, b)] -> Result [(a, b)]
insertLookup _ x [] = Right $ x : []
insertLookup f (a, b) ((c, d) : xs) = if a == c
  then if b == d then Right $ (c, d) : xs else Left $ f a b d
  else (\x -> (c, d) : x) <$> insertLookup f (a, b) xs

lookupTerm :: Int -> TermLookup -> Result Term
lookupTerm x terms = toResult (MissingTerm x) $ lookup x $ snd terms

lookupSubContext :: Int -> TermLookup -> Result (Int, Context)
lookupSubContext x terms = toResult (MissingSubContext x) $ lookup x $ fst terms

combineTermLookup :: TermLookup -> TermLookup -> TermLookup
combineTermLookup (ctxsA, termsA) (ctxsB, termsB) = (ctxsA ++ ctxsB, termsA ++ termsB)

createJudgement :: TermLookup -> JudgementOut -> Result Judgement
createJudgement terms (Ctx ctx) = Ctx <$> createContext terms ctx
createJudgement terms (Membership ctx termA termB)
  = Membership <$> createContext terms ctx <*> createTerm terms termA <*> createTerm terms termB
createJudgement terms (DefEq ctx termA termB termC) = DefEq
  <$> createContext terms ctx
  <*> createTerm terms termA
  <*> createTerm terms termB
  <*> createTerm terms termC

createContext :: TermLookup -> ContextOut -> Result Context
createContext _ [] = Right []
createContext terms (NewGeneric term : xs) = (:) <$> createTerm terms term <*> createContext terms xs
createContext terms (SubContextOut x : xs) = (++) . snd <$> lookupSubContext x terms <*> createContext terms xs
createContext terms (SubContextReplace x term termId : xs) = do
  (from, subCtx) <- lookupSubContext x terms
  replacedSubContext <- (flip fmap subCtx) <$> (replaceTerm termId <$> createTerm terms term)
  ctx <- createContext terms xs
  (++ ctx) <$> moveContext from (length ctx) replacedSubContext

moveContext :: Int -> Int -> Context -> Result Context
moveContext from to = sequence . fmap (moveTerm from to)

moveTerm :: Int -> Int -> Term -> Result Term
moveTerm from to (Generic x) = if x < from && x > to then Left $ MissingTermInOutput x else Right (Generic x)
moveTerm from to (Instance termType terms) = (\x -> Instance termType x) <$> sequence (moveTerm from to <$> terms)
moveTerm _ _ (Constant x) = Right $ Constant x
moveTerm _ _ (Internal x) = Right $ Internal x

createTerm :: TermLookup -> TermOut -> Result Term
createTerm terms (GenericOut x) = lookupTerm x terms
createTerm terms (InstanceOut termType parts ) = do
  _ <- assertResult (IncorrectTypeInputsOut termType parts) $ (typeSize termType) == (length parts)
  newParts <- sequence $ createTerm terms <$> parts
  return $ Instance termType newParts
createTerm  terms (InstanceConsume termType parts x) = do
  _ <- assertResult (IncorrectTypeInputsOut termType parts) $ (typeSize termType) == (length parts)
  newParts <- sequence $ createTerm terms <$> parts
  return $ Instance termType (consumeTerm 0 x <$> newParts)
createTerm  terms (GenericReplace x term termId) = replaceTerm termId <$> createTerm terms term <*> lookupTerm x terms
createTerm  terms (SubContextHeadTerm x) = headResult (UnexpectedEmptySubContext x) =<< snd <$> lookupSubContext x terms
createTerm  terms (SubContextHeadGeneric x) = Generic . (+(-1)) . length . snd <$> lookupSubContext x terms -- TODO Now only supports head of first sub context
createTerm _ (ConstantOut x) = Right $ Constant x

replaceTerm :: Int -> Term -> Term -> Term
replaceTerm termId term (Generic x) = if x == termId then term else Generic x
replaceTerm termId term (Instance termType terms) = Instance termType (replaceTerm termId term <$> terms)
replaceTerm _ _ (Constant x) = Constant x
replaceTerm _ _ (Internal x) = Internal x

consumeTerm :: Int -> Int -> Term -> Term
consumeTerm depth termId (Generic x) = if x == termId then Internal depth else Generic x
consumeTerm depth termId (Instance termType terms) = Instance termType (consumeTerm (depth + 1) termId <$> terms)
consumeTerm _ _ (Constant x) = Constant x
consumeTerm _ _ (Internal x) = Internal x

collectJudgements :: [(Int, Int)] -> [JudgementIn] -> [Judgement] -> Result TermLookup
collectJudgements lengths = join .: (
  fmap (mergeTermLookup . foldl combineTermLookup emptyLookup)
  .: (sequence .: zipWith (collectJudgement lengths)))

collectJudgement :: [(Int, Int)] -> JudgementIn -> Judgement -> Result TermLookup
collectJudgement lengths (Ctx ctxIn) (Ctx ctx) = collectContext lengths ctxIn ctx
collectJudgement lengths (Membership ctxIn termAIn termBIn) (Membership ctx termA termB)
  = let terms = [collectContext lengths ctxIn ctx, collectTermFull termAIn termA, collectTermFull termBIn termB]
    in foldl1 combineTermLookup <$> sequence terms
collectJudgement lengths (DefEq ctxIn termAIn termBIn termCIn) (DefEq ctx termA termB termC)
  = let terms = [ collectContext lengths ctxIn ctx
                  , collectTermFull termAIn termA
                  , collectTermFull termBIn termB
                  , collectTermFull termCIn termC]
    in foldl1 combineTermLookup <$> sequence terms
collectJudgement _ a b = Left $ IncompatibleJudgements a b

collectContext :: [(Int, Int)] -> ContextIn -> Context -> Result TermLookup
collectContext _ [] [] = Right ([], [])
collectContext _ [] (x : _) = Left $ UnconsumedTerm x
collectContext _ [SubContextIn x] ctx = Right ([(x, (0, ctx))], [])
collectContext lengths (SubContextIn x : ctxIn) ctx = do
  len <- toResult (SubContextLengthUnspecified x) $ lookup x lengths
  let actualLength = length ctx
  _ <- assertResult (MissingTermsForSubContext x $ actualLength - len) $ actualLength >= len
  let (ctxA, ctxB) = splitAt len ctx
  (collectedContexts, collectedTerms) <- collectContext lengths ctxIn ctxB
  return ((x, (length ctxB, ctxA)) : collectedContexts, collectedTerms)
collectContext _ (OfTypeIn x _ : _) [] = Left $ MissingTerm x
collectContext lengths (OfTypeIn x termIn : ctxIn) (term : ctx) = do
  (collectedContexts, collectedRemainingTerms) <- collectContext lengths ctxIn ctx
  collectedTerms <- collectTerm termIn term
  return (collectedContexts, (x, Generic $ length ctx) : collectedTerms ++ collectedRemainingTerms)

collectTermFull :: Term -> Term -> Result TermLookup
collectTermFull x y = (\a -> ([], a)) <$> collectTerm x y

collectTerm :: Term -> Term -> Result [(Int, Term)]
collectTerm (Generic x) term = Right [(x, term)]
collectTerm (Constant x) (Constant y) = if x == y then Left $ WrongConstant x y else Right []
collectTerm (Instance type1 termsFormat) (Instance type2 termsIn) = do
  _ <- assertResult (IncompatibleType type1 type2) $ type1 == type2
  _ <- assertResult (IncorrectTypeInputs type1 termsFormat) $ typeSize type1 == length termsFormat
  _ <- assertResult (IncorrectTypeInputs type1 termsIn) $ typeSize type1 == length termsIn
  fmap concat $ sequence $ zipWith collectTerm termsFormat termsIn
collectTerm a b = Left $ IncompatibleTerms a b

assertResult :: Error -> Bool -> Result ()
assertResult _ True = Right ()
assertResult err False = Left err

headResult :: Error -> [a] -> Result a
headResult _ (x : _) = Right x
headResult err [] = Left err

toResult :: a -> Maybe b -> Either a b
toResult _ (Just b) = Right b
toResult a Nothing = Left a

type Result x = Either Error x
data Error
  = ConflictingTerms Int Term Term
  | ConflictingSubContexts Int Context Context
  | MissingSubContext Int
  | MissingTerm Int
  | MissingTermInOutput Int
  | IncorrectTypeInputs Type [Term]
  | IncorrectTypeInputsOut Type [TermOut]
  | UnexpectedEmptySubContext Int
  | IncompatibleJudgements JudgementIn Judgement
  | IncompatibleTerms Term Term
  | IncompatibleType Type Type
  | UnconsumedTerm Term
  | SubContextLengthUnspecified Int
  | MissingTermsForSubContext Int Int -- id, amounts missing
  | WrongConstant Int Int
  deriving (Show, Eq)
