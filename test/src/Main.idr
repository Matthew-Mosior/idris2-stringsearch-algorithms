module Main

import BoyerMoore
import BoyerMoore.Internal
import DFA
import DFA.Internal
import KnuthMorrisPratt
import KnuthMorrisPratt.Internal
import Utils

import Hedgehog

%default total

main : IO ()
main = test
  [ Utils.props_ANPANMAN
  , Utils.props_ABCABC
  , BoyerMoore.props
  , BoyerMoore.Internal.props
  , DFA.props
  , DFA.Internal.props
  , KnuthMorrisPratt.props
  , KnuthMorrisPratt.Internal.props
  ]
