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
  , TermOut (..)
  , apply
) where

import Data.List
import Control.Monad

data Type = Type { typeSize :: Int, typeId :: Int } deriving Show

instance Eq Type where
  x == y = typeId x == typeId y

--            context index
data Term = Generic Int | Instance {typeOf :: Type, instanceTerms :: [Term]} | Constant Int | Internal Int deriving (Eq, Show)

type Context = [Term]

--           Context is good | Context implies Term is of type Term | Context impliess that Term and Term are equal of type Term
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
  deriving Show

data ContextPartIn
  = OfTypeIn Int Term
  | SubContextIn Int
  deriving Show

data ContextPartOut
  = NewGeneric TermOut
  | SubContextOut Int
  | SubContextReplace {contextId :: Int, ctxReplacingTerm :: TermOut, ctxReplacedId :: Int}
  deriving Show

type ContextIn = [ContextPartIn]
type ContextOut = [ContextPartOut]

type JudgementIn = JudgementType ContextIn Term
type JudgementOut = JudgementType ContextOut TermOut

data Rule = Rule {assumptions :: [JudgementIn], conclusion :: JudgementOut} deriving Show

apply :: Rule -> [Int] -> [Judgement] -> Maybe Judgement
apply rule lengths contexts = do
  termLookup <- collectJudgements lengths (assumptions rule) contexts
  createJudgement termLookup $ conclusion rule

type TermLookup = ([(Int, (Int, Context))], [(Int, Term)])

emptyLookup :: TermLookup
emptyLookup = ([], [])

mergeTermLookup :: TermLookup -> Maybe TermLookup
mergeTermLookup (a, b) = do
  mergedA <- mergeLookup a
  mergedB <- mergeLookup b
  return (mergedA, mergedB)

mergeLookup :: (Eq a, Eq b) => [(a, b)] -> Maybe [(a, b)]
mergeLookup = foldl (\a b -> join $ (flip insertLookup <$> a) ?? b) $ Just []

insertLookup :: (Eq a, Eq b) => (a, b) -> [(a, b)] -> Maybe [(a, b)]
insertLookup x [] = Just $ x : []
insertLookup (a, b) ((c, d) : xs) = if a == c
  then if b == d then Just $ (c, d) : xs else Nothing
  else (\x -> (c, d) : x) <$> insertLookup (a, b) xs

combineTermLookup :: TermLookup -> TermLookup -> TermLookup
combineTermLookup (ctxsA, termsA) (ctxsB, termsB) = (ctxsA ++ ctxsB, termsA ++ termsB)

createJudgement :: TermLookup -> JudgementOut -> Maybe Judgement
createJudgement terms (Ctx ctx) = Ctx <$> createContext terms ctx
createJudgement terms (Membership ctx termA termB)
  = Membership <$> createContext terms ctx <*> createTerm terms termA <*> createTerm terms termB
createJudgement terms (DefEq ctx termA termB termC) = DefEq
  <$> createContext terms ctx
  <*> createTerm terms termA
  <*> createTerm terms termB
  <*> createTerm terms termC

createContext :: TermLookup -> ContextOut -> Maybe Context
createContext _ [] = Just []
createContext terms (NewGeneric term : xs) = (:) <$> createTerm terms term <*> createContext terms xs
createContext terms (SubContextOut x : xs) = (++) . snd <$> lookup x (fst terms) <*> createContext terms xs
createContext terms (SubContextReplace { contextId = x, ctxReplacingTerm = term, ctxReplacedId = termId } : xs) = do
  (from, subCtx) <- lookup x (fst terms)
  replacedSubContext <- (flip fmap subCtx) <$> (replaceTerm termId <$> createTerm terms term)
  ctx <- createContext terms xs
  (++ ctx) <$> moveContext from (length ctx) replacedSubContext

moveContext :: Int -> Int -> Context -> Maybe Context
moveContext from to = sequence . fmap (moveTerm from to)

moveTerm :: Int -> Int -> Term -> Maybe Term
moveTerm from to (Generic x) = if x < from && x > to then Nothing else Just (Generic x)
moveTerm from to (Instance { typeOf = termType, instanceTerms = terms })
  = (\x -> Instance {typeOf = termType, instanceTerms = x}) <$> sequence (moveTerm from to <$> terms)
moveTerm _ _ (Constant x) = Just $ Constant x
moveTerm _ _ (Internal x) = Just $ Internal x

createTerm :: TermLookup -> TermOut -> Maybe Term
createTerm terms (GenericOut x)= lookup x $ snd terms
createTerm terms (InstanceOut { typeOfTerm = termType, termParts = parts }) = do
  _ <- assertMaybe $ (typeSize termType) == (length parts)
  newParts <- sequence $ createTerm terms <$> parts
  return $ Instance { typeOf = termType, instanceTerms = newParts }
createTerm  terms (InstanceConsume { typeOfTerm = termType, termParts = parts, consumeId = x }) = do
  _ <- assertMaybe $ (typeSize termType) == (length parts)
  newParts <- sequence $ createTerm terms <$> parts
  return $ Instance { typeOf = termType, instanceTerms = consumeTerm 0 x <$> newParts }
createTerm  terms (GenericReplace {genericId = x, termReplacingTerm = term, termReplacedId = termId})
  = replaceTerm termId <$> createTerm terms term <*> (lookup x $ snd terms)
createTerm  terms (SubContextHeadTerm x) = headMaybe =<< snd <$> lookup x (fst terms)
createTerm  terms (SubContextHeadGeneric x) = Generic . (+(-1)) . length . snd <$> lookup x (fst terms) -- TODO Now only supports head of first sub context
createTerm _ (ConstantOut x) = Just $ Constant x

replaceTerm :: Int -> Term -> Term -> Term
replaceTerm termId term (Generic x) = if x == termId then term else Generic x
replaceTerm termId term (Instance {typeOf = termType, instanceTerms = terms})
  = Instance { typeOf = termType, instanceTerms = replaceTerm termId term <$> terms}
replaceTerm _ _ (Constant x) = Constant x
replaceTerm _ _ (Internal x) = Internal x

consumeTerm :: Int -> Int -> Term -> Term
consumeTerm depth termId (Generic x) = if x == termId then Internal depth else Generic x
consumeTerm depth termId (Instance {typeOf = termType, instanceTerms = terms})
  = Instance { typeOf = termType, instanceTerms = consumeTerm (depth + 1) termId <$> terms}
consumeTerm _ _ (Constant x) = Constant x
consumeTerm _ _ (Internal x) = Internal x

collectJudgements :: [Int] -> [JudgementIn] -> [Judgement] -> Maybe TermLookup
collectJudgements lengths = join .: (
  fmap (mergeTermLookup . foldl combineTermLookup emptyLookup)
  .: (sequence .: zipWith (collectJudgement lengths)))

collectJudgement :: [Int] -> JudgementIn -> Judgement -> Maybe TermLookup
collectJudgement lengths (Ctx ctxIn) (Ctx ctx) = collectContext lengths ctxIn ctx
collectJudgement lengths (Membership ctxIn termAIn termBIn) (Membership ctx termA termB)
  = let lookups = [collectContext lengths ctxIn ctx, collectTermFull termAIn termA, collectTermFull termBIn termB]
    in foldl1 combineTermLookup <$> sequence lookups
collectJudgement lengths (DefEq ctxIn termAIn termBIn termCIn) (DefEq ctx termA termB termC)
  = let lookups = [ collectContext lengths ctxIn ctx
                  , collectTermFull termAIn termA
                  , collectTermFull termBIn termB
                  , collectTermFull termCIn termC]
    in foldl1 combineTermLookup <$> sequence lookups
collectJudgement _ _ _ = Nothing

collectContext :: [Int] -> ContextIn -> Context -> Maybe TermLookup
collectContext _ [] [] = Just ([], [])
collectContext _ [] (_ : _) = Nothing
collectContext _ [SubContextIn x] ctx = Just ([(x, (0, ctx))], [])
collectContext lengths (SubContextIn x : ctxIn) ctx = do
  len <- lengths !? x
  _ <- assertMaybe $ length ctx >= len
  let (ctxA, ctxB) = splitAt len ctx
  (collectedContexts, collectedTerms) <- collectContext lengths ctxIn ctxB
  return ((x, (length ctxB, ctxA)) : collectedContexts, collectedTerms)
collectContext _ (OfTypeIn _ _ : _) [] = Nothing
collectContext lengths (OfTypeIn x termIn : ctxIn) (term : ctx) = do
  (collectedContexts, collectedRemainingTerms) <- collectContext lengths ctxIn ctx
  collectedTerms <- collectTerm termIn term
  return (collectedContexts, (x, Generic $ length ctx) : collectedTerms ++ collectedRemainingTerms)

collectTermFull :: Term -> Term -> Maybe TermLookup
collectTermFull x y = (\a -> ([], a)) <$> collectTerm x y

collectTerm :: Term -> Term -> Maybe [(Int, Term)]
collectTerm (Generic x) term = Just [(x, term)]
collectTerm (Constant x) (Constant y) = if x == y then Nothing else Just []
collectTerm (Instance {typeOf = type1, instanceTerms = termsFormat}) (Instance {typeOf = type2, instanceTerms = termsIn}) = do
  _ <- assertMaybe $ type1 == type2 && typeSize type1 == length termsFormat && typeSize type1 == length termsIn
  fmap concat $ sequence $ zipWith collectTerm termsFormat termsIn
collectTerm _ _ = Nothing

assertMaybe :: Bool -> Maybe ()
assertMaybe True = Just ()
assertMaybe False = Nothing

(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) f g a b = f $ g a b

(??) :: Functor f => f (a -> b) -> a -> f b
(??) ff x = (\f -> f x) <$> ff

headMaybe :: [a] -> Maybe a
headMaybe (x : _) = Just x
headMaybe [] = Nothing
