module Main (main) where

import Test.DocTest

main :: IO ()
main = doctest ["-isrc", "src/Data/IntSet/Dom.hs"]
