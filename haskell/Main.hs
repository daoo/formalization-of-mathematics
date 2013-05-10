module Main where

import Examples
import ToomCook

main = do
  a <- read `fmap` getLine
  b <- read `fmap` getLine
  print $ toomCook wikiSettings a b
