{-# LANGUAGE LambdaCase #-}
module ToomCookNat where

import Debug.Trace
import Test.QuickCheck

n = 987654321987654321098
m = 1234567890123456789012

degree :: Integer -> Integer
degree = \case
  0 -> 0
  n -> 1 + degree (n `div` 10)

baseExponent :: Integer -> Integer -> Integer
baseExponent n m = 1 + max (degree n `div` 3) (degree m `div` 3)

split :: Integer -> Integer -> [Integer]
split b n = let (n', x0)  = n `divMod` b
                (n'', x1) = n' `divMod` b
                (_, x2)   = n'' `divMod` b
             in [x2, x1, x0]

merge :: Integer -> [Integer] -> Integer
merge b [x2, x1, x0] = x0 + (x1 * b) + (x2 * b * b)

evaluate :: [Integer] -> [Integer]
evaluate [n2, n1, n0] =
  [ n0
  , n0 + n1 + n2
  , n0 - n1 + n2
  , n0 - 2*n1 + 4*n2
  , n2
  ]

pointwise :: [Integer] -> [Integer] -> [Integer]
pointwise [] []         = []
pointwise (p:ps) (q:qs) = p `toomCook3` q : pointwise ps qs
pointwise _ _           = error "pointwise: not the same length"

between n a b = n >= a && n <= b

toomCook3 :: Integer -> Integer -> Integer
toomCook3 n m | n < 0 && m < 0 = toomCook3 (abs n) (abs m)
toomCook3 n m | n < 0          = negate $ toomCook3 (abs n) m
toomCook3 n m | m < 0          = negate $ toomCook3 n (abs m)

toomCook3 n m | n <= 100 || m <= 100 = n * m

toomCook3 n m =
  let b = 10^(baseExponent n m)
      n' = split b n
      m' = split b m
      r  = pointwise (evaluate n') (evaluate m')
      r' = interpolate r
   in recompose b r'

badMul :: Integer -> Integer -> Integer
badMul 0 _ = 0
badMul n m = m + badMul (n - 1) m

interpolate :: [Integer] -> [Integer]
interpolate [ r0, r1, rn1, rn2, rinf ] =
  let s0 = r0
      s4 = rinf
      s3 = (rn2 - r1) `div` 3
      s1 = (r1 - rn1) `div` 2
      s2 = rn1 - r0
      s3' = (s2 - s3) `div` 2 + 2 * rinf
      s2' = s2 + s1 - s4
      s1' = s1 - s3'
   in [ s0, s1', s2', s3', s4 ]

recompose :: Integer -> [Integer] -> Integer
recompose b = go 1
  where
    go _ []      = 0
    go b' (r:rs) = b' * r + go (b * b') rs

propToomCook3Commutative :: Integer -> Integer -> Bool
propToomCook3Commutative n m = toomCook3 n m == toomCook3 m n

propToomCook3Associative :: Integer -> Integer -> Integer -> Bool
propToomCook3Associative n m p = toomCook3 n (toomCook3 m p) == toomCook3 (toomCook3 n m) p

propToomCook3Correct :: Integer -> Integer -> Bool
propToomCook3Correct n m = n * m == toomCook3 n m

propSplitCorrect :: Positive Integer -> Bool
propSplitCorrect (Positive n) = n == merge 10 (split 10 n)
