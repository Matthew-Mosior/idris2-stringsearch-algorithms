module Main

import KnuthMorrisPratt
import Utils

import Hedgehog

%default total

main : IO ()
main = test
  [ Utils.props
  , KnuthMorrisPratt.props
  ]
