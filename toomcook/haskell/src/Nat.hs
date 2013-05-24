{-# LANGUAGE MagicHash, UnboxedTuples, BangPatterns #-}
module Nat where

import Data.Word

-- Little endian
data Nat = Zero
         | Term {-# UNPACK #-} !Word Nat
  deriving Show

zero, one :: Nat
zero = Zero
one  = Term 1 Zero

add :: Nat -> Nat -> Nat
add = go
  where
    go n Zero = n
    go Zero m = m

    go (Term n ns) (Term m ms) = Term (n + m) $ add ns ms

instance Num Nat where
  (+) = add
  (-) = undefined
  (*) = undefined

  abs = id

  signum Zero = zero
  signum _    = one

  fromInteger i = if i < mbound
    then Term (fromIntegral i) Zero
    else case i `quotRem` mbound of
      (q, r) -> Term (fromIntegral r) (fromInteger q)

tbits :: Int
tbits = bitSize (0 :: Word)

apa :: Nat -> Integer
apa = go 1
  where
    go :: Integer -> Nat -> Integer
    go _ Zero        = 0
    go b (Term n ns) = b*(fromIntegral n) + go (b*mbound) ns
