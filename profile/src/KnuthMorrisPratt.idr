module KnuthMorrisPratt

import Data.ByteString.Search.KnuthMorrisPratt

import Data.ByteString
import Profile

export
kmpfavoredpat : ByteString
kmpfavoredpat =
  Data.ByteString.pack $
    map (cast {to=Bits8}) $
      Prelude.unpack "ABABACABABAC"

export
kmpfavoredtarget : ByteString
kmpfavoredtarget =
  Data.ByteString.pack $
    map (cast {to=Bits8}) $
      Prelude.unpack "ABABACABABACABABACABABACABABACABABAC"

export
kmppathologicalpat : ByteString
kmppathologicalpat =
  Data.ByteString.pack $
    map (cast {to=Bits8}) $
      Prelude.unpack "ABCDEFGHIJKL"

export
kmppathologicaltarget : ByteString
kmppathologicaltarget =
  Data.ByteString.pack $
    map (cast {to=Bits8}) $
      Prelude.unpack "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
