module Main

import BoyerMoore
import DFA
import KnuthMorrisPratt
import Utils

import Hedgehog

%default total

main : IO ()
main = test
  [ Utils.props_ANPANMAN
  , Utils.props_ABCABC
  , BoyerMoore.props
  , DFA.props
  , KnuthMorrisPratt.props
  ]
