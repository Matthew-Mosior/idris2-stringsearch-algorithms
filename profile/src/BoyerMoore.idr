module BoyerMoore

import Data.ByteString.Search.BoyerMoore

import Data.ByteString
import Profile

export
bmfavoredpat : ByteString
bmfavoredpat =
  Data.ByteString.pack $
    map (cast {to=Bits8}) $
      Prelude.unpack "ZEBRAC"

export
bmfavoredtarget : ByteString
bmfavoredtarget =
  Data.ByteString.pack $
    map (cast {to=Bits8}) $
      Prelude.unpack "TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT"

export
bmpathologicalpat : ByteString
bmpathologicalpat =
  Data.ByteString.pack $
    map (cast {to=Bits8}) $
      Prelude.unpack "AAAAAAAB"

export
bmpathologicaltarget : ByteString
bmpathologicaltarget =
  Data.ByteString.pack $
    map (cast {to=Bits8}) $
      Prelude.unpack "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
