module Main where

import Criterion.Main
import Settings
import ToomCook

main :: IO ()
main = defaultMain $
  map (\i -> bench (show i) $ whnf (\j -> toomCook toom3 j j) i)
    [100000, 100100..200000]
