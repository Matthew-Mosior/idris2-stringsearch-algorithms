||| Fast Knuth-Morris-Pratt search of ByteStrings
module Data.ByteString.Search.KnuthMorrisPratt

import Data.Array.Core
import Data.Array.Mutable
import Data.Bits
import Data.ByteString
import Data.Linear.Ref1
import Data.So

%hide Data.Buffer.Core.get
%hide Data.Buffer.Core.set

%default total

||| Returns list of match starting positions of a pattern
||| (0-based) across the list of `ByteStrings`.
export
matcher :  Bool
        -> ByteString
        -> List ByteString
        -> F1 s (List Nat)
matcher overlap pat chunks t =
  case null pat of
    True  =>
      go 0 chunks
    False =>
  where
    searcher :  Nat
             -> Nat
             -> List ByteString
             -> F1 s (List Nat)
    searcher _     _      []          t =
      [] # t
    searcher prior patpos (str::rest) t =
      
