module Main where

import Settings
import Test.QuickCheck
import ToomCook

-- |Merge a splitted integer using some base
-- This is the inverse of split.
{-merge :: Integer -> [Integer] -> Integer-}
{-merge b = recompose b . reverse-}

genK :: Gen Int
genK = choose (2, 10)

genNum :: Gen Integer
genNum = choose (100000000, 999999999)

propToomCookCorrect :: ToomCook -> Property
propToomCookCorrect t = forAll genNum $ \n -> forAll genNum $ \m ->
  toomCook t n m == n * m

{-propSplitCorrect :: Property-}
{-propSplitCorrect = forAll genK $ \k -> forAll genNum $ \n ->-}
  {-let b = 10^baseExponent k n n in n == merge b (split k b n)-}

main :: IO ()
main = do
  quickCheck (propToomCookCorrect karatsuba)
  quickCheck (propToomCookCorrect toom3)
  quickCheck (propToomCookCorrect toom4)
  {-quickCheck propSplitCorrect-}
