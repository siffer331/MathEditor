module Util where

(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) f g a b = f $ g a b

(??) :: Functor f => f (a -> b) -> a -> f b
(??) ff x = (\f -> f x) <$> ff

(<|>) :: (Int -> a -> b) -> [a] -> [b]
(<|>) ff = fst . iMap ff where
  iMap :: (Int -> a -> b) -> [a] -> ([b], Int)
  iMap _ [] = ([], 0)
  iMap f (a:as) = let (bs, i) = iMap f as in (f i a : bs, i + 1)

(<||>) :: (Int -> a -> b) -> [a] -> [b]
(<||>) = flip iMap 0 where
  iMap :: (Int -> a -> b) -> Int -> [a] -> [b]
  iMap _ _ [] = []
  iMap f i (a:as) = f i a : iMap f (i + 1) as

