{-# LANGUAGE LambdaCase, BangPatterns, MagicHash, UnboxedTuples #-}
module ImplOpt where

import Control.Exception (assert)
import Data.Ratio
import GHC.Integer
import ToomCook

matVecMul :: Num a => [[a]] -> [a] -> [a]
matVecMul mat vec = map (sum . zipWith (*) vec) mat

matVecMulRat :: [[Rational]] -> [Integer] -> [Integer]
matVecMulRat mat vec = map numerator $ map (sum . zipWith f vec) mat
  where
    f a b = fromInteger a * b

{-# INLINE log10 #-}
log10 :: Integer -> Integer
log10 n = assert (n >= 0) $ go 0 n
  where
    go !acc  0  = acc
    go !acc !n' = go (acc + 1) (n' `quot` 10)

{-# INLINE baseExponent #-}
baseExponent :: Int -> Integer -> Integer -> Integer
baseExponent k n m = assert (k > 0) $
  1 + max
    (log10 n `quotInteger` fromIntegral k)
    (log10 m `quotInteger` fromIntegral k)

{-# INLINE split #-}
-- |Split an integer into a big-endian list of integers using a given base
split :: Int -> Integer -> Integer -> [Integer]
split k b = assert (b > 0) $ go k []
  where
    go  0  acc _ = acc
    go !k' acc n = case n `quotRemInteger` b of
      (# n', x' #) -> go (k'-1) (x':acc) n'

{-# INLINE evaluate #-}
-- |Evaluate the splits using the evaluation matrix
-- Note that since the splitlist is big-endian, either we have
-- to reverse each row of the evaluation matrix, or reverse the
-- splitlist.
evaluate :: [[Integer]] -> [Integer] -> [Integer]
evaluate = matVecMul

{-# INLINE interpolate #-}
interpolate :: [[Rational]] -> [Integer] -> [Integer]
interpolate = matVecMulRat

{-# INLINE recompose #-}
recompose :: Integer -> [Integer] -> Integer
recompose b = go 1 0
  where
    go  _  !acc []     = acc
    go !b' !acc (x:xs) = go (b * b') (acc + b' * x) xs

{-# INLINE toomCookRec #-}
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
