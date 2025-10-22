module Main

import Hedgehog
import Utils

%default total

main : IO ()
main = test
  [ Utils.props
  ]
