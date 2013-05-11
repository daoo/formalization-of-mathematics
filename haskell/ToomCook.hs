{-# LANGUAGE LambdaCase, BangPatterns,
             MagicHash, UnboxedTuples #-}
module ToomCook where

import Control.Exception (assert)
import Data.List
import Data.Ratio
import GHC.Base
import GHC.Integer

data ToomCook = ToomCook
  { toomK :: Int
  , toomMat :: [[Integer]]
  , toomInvMat :: [[Rational]]
  }

{-# INLINE ratMulUnsafe #-}
ratMulUnsafe :: Integer -> Rational -> Integer
ratMulUnsafe a b = assert (denominator r == 1) (numerator r)
  where r = (fromIntegral a) * b

matVecMul :: Num a => [[a]] -> [a] -> [a]
matVecMul mat vec = map (sum . zipWith (*) vec) mat

matVecMul' :: [[Rational]] -> [Integer] -> [Integer]
matVecMul' mat vec = map (sum . zipWith ratMulUnsafe vec) mat

log10 :: Integer -> Integer
log10 = go 0
  where
    go !acc  0 = acc
    go !acc !n = go (acc + 1) (n `quot` 10)

{-# INLINE baseExponent #-}
baseExponent :: Int -> Integer -> Integer -> Integer
baseExponent k n m = assert (k > 0) $
  1 + max
    (log10 n `quotInteger` fromIntegral k)
    (log10 m `quotInteger` fromIntegral k)

split :: Int -> Integer -> Integer -> [Integer]
split k b = assert (b > 0) $ go k []
  where
    go  0  acc _ = acc
    go !k' acc n = case n `quotRemInteger` b of
      (# n', x' #) -> go (k' - 1) (x' : acc) n'

{-# INLINE merge #-}
merge :: Integer -> [Integer] -> Integer
merge b = recompose b . reverse

evaluate :: [[Integer]] -> [Integer] -> [Integer]
evaluate mat vec = matVecMul mat (reverse vec)

interpolate :: [[Rational]] -> [Integer] -> [Integer]
interpolate = matVecMul'

recompose :: Integer -> [Integer] -> Integer
recompose b = go 1 0
  where
    go  _  !acc []     = acc
    go !b' !acc (x:xs) = go (b * b') (acc + b' * x) xs

toomCook :: ToomCook -> Integer -> Integer -> Integer
toomCook !t !n !m | n < 0 && m < 0 = toomCook t (abs n) (abs m)
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
