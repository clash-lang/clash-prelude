module Main where

import Test.DocTest (doctest)

main :: IO ()
main = doctest ["-isrc","-optP-I","-optPinclude","CLaSH.Prelude","CLaSH.Examples","CLaSH.Tutorial"]
