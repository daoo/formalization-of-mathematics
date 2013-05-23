{-# LANGUAGE BangPatterns, MagicHash, UnboxedTuples #-}
module ToomCook
  ( ToomCook(..)
  , baseExponent
  , split
  , evaluate
  , interpolate
  , recompose
  , toomCookRec
  , toomCook
  ) where

import Control.Exception (assert)
import GHC.Exts
import GHC.Integer
import GHC.Integer.Logarithms

data ToomCook = ToomCook
  { toomK :: Int
  , toomMat :: [[Integer]]
  , toomInvMat :: [(Integer, [Integer])]
  }

dot :: Num a => [a] -> [a] -> a
dot = go 0
  where
    go !acc (x:xs) (y:ys) = go (acc + x * y) xs ys
    go !acc _      _      = acc

matVecMul :: Num a => [[a]] -> [a] -> [a]
matVecMul mat vec = map (dot vec) mat

-- |Special Matrix, vector multiplication
-- Each row is devided by the factor after the dot product.
matVecMulRat :: [(Integer, [Integer])] -> [Integer] -> [Integer]
matVecMulRat mat vec = map (\(f, r) -> dot vec r `quot` f) mat

baseExponent :: Int -> Integer -> Integer -> Int
baseExponent k n m = assert (k > 0) $
  1 + max
    (integerLogBase# 10 n `unsafeQuot` k)
    (integerLogBase# 10 m `unsafeQuot` k)
  where
    unsafeQuot x (I# y) = I# (quotInt# x y)

-- |Split an integer into a big-endian list of integers using a given base
split :: Int -> Integer -> Integer -> [Integer]
split k b = assert (b > 0) $ go k []
  where
    go  0  acc _ = acc
    go !k' acc n = case n `quotRemInteger` b of
      (# n', x' #) -> go (k'-1) (x':acc) n'

-- |Evaluate the splits using the evaluation matrix
-- Note that since the splitlist is big-endian, either we have
-- to reverse each row of the evaluation matrix, or reverse the
-- splitlist.
evaluate :: [[Integer]] -> [Integer] -> [Integer]
evaluate = matVecMul

interpolate :: [(Integer, [Integer])] -> [Integer] -> [Integer]
interpolate = matVecMulRat

recompose :: Integer -> [Integer] -> Integer
recompose b = go 1 0
  where
    go  _  !acc []     = acc
    go !b' !acc (x:xs) = go (b * b') (acc + b' * x) xs

toomCookRec :: ToomCook -> Integer -> Integer -> Integer
toomCookRec !t !n !m = if n <= 100 || m <= 100
  then n * m
  else let b   = 10^(baseExponent (toomK t) n m)
           n'  = split (toomK t) b n
           m'  = split (toomK t) b m
           n'' = evaluate (toomMat t) n'
           m'' = evaluate (toomMat t) m'
           r   = zipWith (toomCookRec t) n'' m''
           r'  = interpolate (toomInvMat t) r
        in recompose b r'

toomCook :: ToomCook -> Integer -> Integer -> Integer
toomCook t n m | n < 0 && m < 0 = toomCookRec t (abs n) (abs m)
               | n < 0          = negate $ toomCookRec t (abs n) m
               | m < 0          = negate $ toomCookRec t n (abs m)
               | otherwise      = toomCookRec t n m
