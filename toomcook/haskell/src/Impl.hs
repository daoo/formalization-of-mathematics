module Impl where

import Control.Exception (assert)
import Data.Ratio
import ToomCook

matVecMul :: Num a => [[a]] -> [a] -> [a]
matVecMul mat vec = map (sum . zipWith (*) vec) mat

log10 :: Integer -> Integer
log10 n = assert (n >= 0) $ go 0 n
  where
    go acc 0  = acc
    go acc n' = go (acc + 1) (n' `quot` 10)

baseExponent :: Int -> Integer -> Integer -> Integer
baseExponent k n m = assert (k > 0) $
  1 + max
    (log10 n `quot` fromIntegral k)
    (log10 m `quot` fromIntegral k)

-- |Split an integer into a big-endian list of integers using a given base
split :: Int -> Integer -> Integer -> [Integer]
split k b = assert (b > 0) $ go k []
  where
    go 0  acc _ = acc
    go k' acc n = case n `quotRem` b of
      (n', x') -> go (k'-1) (x':acc) n'

-- |Merge a splitted integer using some base
-- This is the inverse of split.
merge :: Integer -> [Integer] -> Integer
merge b = recompose b . reverse

-- |Evaluate the splits using the evaluation matrix
-- Note that since the splitlist is big-endian, either we have
-- to reverse each row of the evaluation matrix, or reverse the
-- splitlist.
evaluate :: [[Integer]] -> [Integer] -> [Integer]
evaluate = matVecMul

interpolate :: [[Rational]] -> [Integer] -> [Integer]
interpolate mat vec = map numerator $ matVecMul mat $ map fromInteger vec

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
