module Main where

import Settings
import ToomCook

main :: IO ()
main = do
  a <- read `fmap` getLine
  b <- read `fmap` getLine
  print $ toomCook toom3 a b
