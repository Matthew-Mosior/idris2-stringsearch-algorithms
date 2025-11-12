module Main

import DFA
import KnuthMorrisPratt
import Utils

import Hedgehog

%default total

main : IO ()
main = test
  [ Utils.props
  , DFA.props
  , KnuthMorrisPratt.props
  ]
