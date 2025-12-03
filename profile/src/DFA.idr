module DFA

import Data.ByteString.Search.DFA

import Data.ByteString
import Profile
import System.Random.Pure.StdGen

export
dfapat : ByteString
dfapat =
  Data.ByteString.pack $
    map (cast {to=Bits8}) $
      Prelude.unpack "ABCD"

export
dfatarget : ByteString
dfatarget =
  Data.ByteString.pack $
    map (cast {to=Bits8}) $
      Prelude.unpack "AABCAABCAABCAABCAABCAABC"
