{-# LANGUAGE LambdaCase #-}
module ToomCookNat where

import Data.Ratio

data ToomCook = ToomCook
  { toomK :: Int
  , toomMat :: [[Integer]]
  , toomInvMat :: [[Rational]]
  }

matVecMul :: Num a => [[a]] -> [a] -> [a]
matVecMul mat vec = map (sum . zipWith (*) vec) mat

unsafeToInteger :: Rational -> Integer
unsafeToInteger r | denominator r == 1 = numerator r
                  | otherwise          = error $ show r

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
    go 0  acc _ = acc
    go k' acc n = let (n', x') = n `divMod` b
                   in go (k' - 1) (x' : acc) n'

merge :: Integer -> [Integer] -> Integer
merge b = recompose b . reverse

evaluate :: [[Integer]] -> [Integer] -> [Integer]
evaluate mat vec = matVecMul mat (reverse vec)

interpolate :: [[Rational]] -> [Integer] -> [Integer]
interpolate mat = map unsafeToInteger . matVecMul mat . map toRational

recompose :: Integer -> [Integer] -> Integer
recompose b = go 1 0
  where
    go _  acc []     = acc
    go b' acc (x:xs) = go (b * b') (acc + b' * x) xs

toomCook :: ToomCook -> Integer -> Integer -> Integer
toomCook t n m | n < 0 && m < 0 = toomCook t (abs n) (abs m)
               | n < 0          = negate $ toomCook t (abs n) m
               | m < 0          = negate $ toomCook t n (abs m)

               | n <= 100 || m <= 100 = n * m

               | otherwise =
  let b   = 10^(baseExponent (toomK t) n m)
      n'  = split (toomK t) b n
      m'  = split (toomK t) b m
      n'' = evaluate (toomMat t) n'
      m'' = evaluate (toomMat t) m'
      r   = zipWith (toomCook t) n'' m''
      r'  = interpolate (toomInvMat t) r
   in recompose b r'
