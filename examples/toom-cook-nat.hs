{-# LANGUAGE LambdaCase #-}
module ToomCookNat where

import Data.Ratio
import Test.QuickCheck

matVecMul :: Num a => [[a]] -> [a] -> [a]
matVecMul mat vec = map (sum . zipWith (*) vec) mat

unsafeToInteger :: Rational -> Integer
unsafeToInteger r | denominator r == 1 = numerator r
                  | otherwise          = error $ show r

wikiK :: Int
wikiK = 3

wikiN, wikiM, wikiB :: Integer
wikiN = 987654321987654321098
wikiM = 1234567890123456789012
wikiB = 10^baseExponent wikiK wikiN wikiM

wikiMat :: [[Integer]]
wikiMat = [[1, 0, 0], [1, 1, 1], [1, -1, 1], [1, -2, 4], [0, 0, 1]]

wikiMatInv :: [[Rational]]
wikiMatInv = [ [ 1   , 0   ,  0   ,  0    ,  0]
             , [ 1%2 , 1%3 , -1   ,  1%6  , -2]
             , [-1   , 1%2 ,  1%2 ,  0    , -1]
             , [-1%2 , 1%6 ,  1%2 , -1%6  ,  2]
             , [ 0   , 0   ,  0   ,  0    ,  1]
             ]

degree :: Integer -> Integer
degree = go 0
  where
    go acc 0 = acc
    go acc n = go (acc + 1) (n `div` 10)

baseExponent :: Int -> Integer -> Integer -> Integer
baseExponent k n m = 1 + max (degree n `div` fromIntegral k) (degree m `div` fromIntegral k)

split :: Int -> Integer -> Integer -> [Integer]
split k b = go k []
  where
    go 0 acc _  = acc
    go k' acc m = let (m', x') = m `divMod` b
                   in go (k' - 1) (x' : acc) m'

merge :: Integer -> [Integer] -> Integer
merge b = go 1 0 . reverse
  where
    go _  acc []     = acc
    go b' acc (x:xs) = go (b' * b) (acc + b' * x) xs

evaluate :: [[Integer]] -> [Integer] -> [Integer]
evaluate mat vec = matVecMul mat (reverse vec)

interpolate :: [[Rational]] -> [Integer] -> [Integer]
interpolate mat = map unsafeToInteger . matVecMul mat . map toRational

recompose :: Integer -> [Integer] -> Integer
recompose b = go 1
  where
    go _ []      = 0
    go b' (r:rs) = b' * r + go (b * b') rs

toomCook :: Int -> Integer -> Integer -> Integer
toomCook k n m | n < 0 && m < 0 = toomCook k (abs n) (abs m)
toomCook k n m | n < 0          = negate $ toomCook k (abs n) m
toomCook k n m | m < 0          = negate $ toomCook k n (abs m)

toomCook _ n m | n <= 100 || m <= 100 = n * m

toomCook k n m =
  let b   = 10^(baseExponent 3 n m)
      n'  = split 3 b n
      m'  = split 3 b m
      n'' = evaluate wikiMat n'
      m'' = evaluate wikiMat m'
      r   = zipWith (toomCook k) n'' m''
      r'  = interpolate wikiMatInv r
   in recompose b r'

slowMult :: Integer -> Integer -> Integer
slowMult 0 _ = 0
slowMult n m = m + slowMult (n - 1) m

genK :: Gen Int
genK = choose (2, 10)

genNum :: Gen Integer
genNum = choose (100000, 1000000000)

propToomCookNCommutative :: Property
propToomCookNCommutative = forAll genK $ \k -> forAll genNum $ \n -> forAll genNum $ \m ->
  toomCook k n m == toomCook k m n

propToomCookNAssociative :: Property
propToomCookNAssociative = forAll genK $ \k -> forAll genNum $ \n -> forAll genNum $ \m -> forAll genNum $ \p ->
  toomCook k n (toomCook k m p) == toomCook k (toomCook k n m) p

propToomCookNCorrect :: Property
propToomCookNCorrect = forAll genK $ \k -> forAll genNum $ \n -> forAll genNum $ \m ->
  toomCook k n m == n * m

propSplitCorrect :: Property
propSplitCorrect = forAll genK $ \k -> forAll genNum $ \n ->
  let b = 10^baseExponent k n n in n == merge b (split k b n)
