module Naive where

import Data.List

toList :: Integer -> [Integer]
toList = go []
  where
    go acc n | n < 10    = n : acc
             | otherwise = go (n `rem` 10 : acc) (n `quot` 10)

naiveMul :: Integer -> Integer -> Integer
naiveMul n m = foldl' s 0 $ map (foldl' s 0) $ map (\x -> map (*x) nl) ml
  where
    nl = toList n
    ml = toList m

    s a b = a*10 + b
