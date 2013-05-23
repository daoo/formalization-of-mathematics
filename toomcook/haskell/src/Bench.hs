module Main where

import Criterion.Main
import Settings
import ToomCook

main :: IO ()
main = defaultMain $
  map (\i -> bench (show i) $ whnf (\j -> toomCook toom3 j j) i)
    [184467440737095516169, 194467440737095516169..284467440737095516169]
