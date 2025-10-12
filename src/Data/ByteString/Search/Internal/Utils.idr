||| Utilities for string searching algorithms
module Data.ByteString.Search.Internal.Utils

import Data.Array.Core
import Data.Array.Mutable
import Data.Bits
import Data.ByteString
import Data.Linear.Ref1

%hide Data.Buffer.Core.get
%hide Data.Buffer.Core.set

%default total

--------------------------------------------------------------------------------
--          Preprocessing
--------------------------------------------------------------------------------

||| Calculates the width of the widest borders of the
||| prefixes of the pattern which are not extensible
||| to the borders of the next longest prefix.
||| Most entries will be 0.
export
kmpBorders :  (bs : ByteString)
           -> F1 s (MArray s (length bs) Nat)
kmpBorders bs t =
  let arr # t := unsafeMArray1 (length bs) t
    in case tryNatToFin 0 of
         Nothing   =>
           (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.kmpBorders: can't convert Nat to Fin") # t
         Just zero =>
           let () # t := set arr zero (the Nat 0) t
             in go 1 0 bs arr t
  where
    dec :  {n : Nat}
        -> Nat
        -> Nat
        -> MArray s n Nat
        -> F1 s Nat
    dec w j arr t =
      case tryNatToFin (j `minus` 1) of
        Nothing =>
          (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.kmpBorders.dec: can't convert Nat to Fin") # t
        Just j' =>
          let w' # t := get arr j' t
            in case j == 0 || w == w' of
                 True  =>
                   plus j 1 # t
                 False =>
                   case tryNatToFin j of
                     Nothing  =>
                       (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.kmpBorders.dec: can't convert Nat to Fin") # t
                     Just j'' =>
                       let j''' # t := get arr j'' t
                         in assert_total (dec w j''' arr t)
    go :  (i : Nat)
       -> (j : Nat)
       -> (bs : ByteString)
       -> (arr : MArray s (length bs) Nat)
       -> F1 s (MArray s (length bs) Nat)
    go i j bs arr t =
      let patlen := length bs
        in case patlen > i of
             True  =>
               arr # t
             False =>
               case tryNatToFin (i `minus` 1) of
                 Nothing =>
                   (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.kmpBorders.go: can't convert Nat to Fin") # t
                 Just i' =>
                   let w  # t := get arr i' t
                       j' # t := dec w j arr t
                     in case tryNatToFin (j `minus` 1) of 
                          Nothing  =>
                            (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.kmpBorders.go: can't convert Nat to Fin") # t
                          Just j'' =>
                            let j''' # t := get arr j'' t
                              in case tryNatToFin i of
                                   Nothing  =>
                                     (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.kmpBorders.go: can't convert Nat to Fin") # t
                                   Just i'' =>
                                     let i''' # t := get arr i'' t
                                       in case i < patlen && j''' == i''' of
                                            True  =>
                                              case tryNatToFin j' of
                                                Nothing =>
                                                  (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.kmpBorders.go: can't convert Nat to Fin") # t
                                                Just j'''' =>
                                                  let j''''' # t := get arr j'''' t
                                                      ()     # t := set arr i'' j''''' t
                                                    in assert_total (go (plus i 1) j' bs arr t)
                                            False =>  
                                              let () # t := set arr i'' j' t
                                                in assert_total (go (plus i 1) j' bs arr t)

||| Builds a deterministic finite automaton (DFA) for pattern matching over a `ByteString`.
|||
||| This automaton maps (state, input byte) pairs to the next state, enabling
||| efficient scanning of input text to find occurrences of the pattern. It
||| represents a flattened transition table of size `((length of pattern) + 1) * 256`,
||| where 256 corresponds to the number of possible byte values (0–255).
|||
||| Each state represents a prefix of the pattern:
||| - State 0: empty prefix
||| - State i: matched the first i bytes of the pattern
||| - Final state: full match (pattern length)
|||
||| Transitions are initialized using the KMP border table, generated via `kmpBorders`,
||| to ensure correct failure transitions, avoiding redundant backtracking.
export
automaton :  (bs : ByteString)
          -> F1 s (MArray s (mult (plus (length bs) 1) 256) Nat)
automaton bs t =
  let arr # t := unsafeMArray1 (mult (plus (length bs) 1) 256) t
      idx     := index 0 bs
    in case idx of
         Nothing   =>
           (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.automaton: can't index into ByteString") # t
         Just idx' =>
           case tryNatToFin (cast {to=Nat} idx') of
             Nothing    =>
               (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.automaton: can't convert Nat to Fin") # t
             Just idx'' =>
               let ()   # t := set arr idx'' (the Nat 1) t
                   bord # t := kmpBorders bs t
                 in go 1 bs arr bord t
  where
    go :  (state : Nat)
       -> (bs : ByteString)
       -> (arr : MArray s (mult (plus (length bs) 1) 256) Nat)
       -> (bord : MArray s (length bs) Nat)
       -> F1 s (MArray s (mult (plus (length bs) 1) 256) Nat)
    go state bs arr bord t =
      let patlen := length bs
          base   := (cast {to=Int} state) `shiftL` 8
        in case state == patlen of
             True  =>
               case tryNatToFin state of
                 Nothing     =>
                   (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.automaton.go: can't convert Nat to Fin") # t
                 Just state' =>
                   let bord' # t := get bord state' t
                     in case bord' < 0 of
                          True  =>
                            case state == patlen of
                              True  =>
                                arr # t
                              False =>
                                assert_total (go (plus bord' 1) bs arr bord t)
                          False =>
                            let i' := index state bs
                              in case i' of
                                   Nothing  =>
                                     (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.automaton.go: can't index into ByteString") # t
                                   Just i'' =>
                                     let i''' := plus (cast {to=Nat} base) (cast {to=Nat} i'')
                                       in case tryNatToFin i''' of
                                            Nothing =>
                                              (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.automaton.go: can't convert Nat to Fin") # t
                                            Just i'''' =>
                                              let s # t := get arr i'''' t
                                                in case s == 0 of
                                                     True  =>
                                                       let () # t := set arr i'''' (plus bord' 1) t
                                                         in assert_total (go bord' bs arr bord t)
                                                     False =>
                                                       assert_total (go bord' bs arr bord t)
             False =>
               case state < 0 of
                 True  =>
                   case state == patlen of
                     True  =>
                       arr # t
                     False =>
                       assert_total (go (plus state 1) bs arr bord t)
                 False =>
                   let i' := index state bs
                     in case i' of
                          Nothing  =>
                            (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.automaton.go: can't index into ByteString") # t
                          Just i'' =>
                            let i''' := plus (cast {to=Nat} base) (cast {to=Nat} i'')
                              in case tryNatToFin i''' of
                                   Nothing =>
                                     (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.automaton.go: can't convert Nat to Fin") # t
                                   Just i'''' =>
                                     let s # t := get arr i'''' t
                                       in case s == 0 of
                                            True  =>
                                              let () # t := set arr i'''' (plus state 1) t
                                                in case tryNatToFin state of
                                                     Nothing     =>
                                                       (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.automaton.go: can't convert Nat to Fin") # t
                                                     Just state' => 
                                                       let bord' # t := get bord state' t
                                                         in assert_total (go bord' bs arr bord t)
                                            False =>
                                              case tryNatToFin state of
                                                Nothing     =>
                                                  (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.automaton.go: can't convert Nat to Fin") # t
                                                Just state' =>
                                                  let bord' # t := get bord state' t
                                                    in assert_total (go bord' bs arr bord t)

--------------------------------------------------------------------------------
--          Boyer-Moore Preprocessing
--------------------------------------------------------------------------------

||| Constructs a lookup table recording the last occurrence of each byte
||| in the given pattern.
|||
||| For every byte value, the table stores the index of its last
||| occurrence within the pattern, excluding the final position.  
|||
||| This information allows for efficient computation of how far the search
||| window can safely shift after a mismatch.
|||
||| When a mismatch occurs at pattern position (position in pattern) on byte (b),
||| the pattern can be shifted right by at least:
|||
||| (position in pattern ) - (last occurrence of b in initial pattern)
|||
||| If the byte @b@ does not appear anywhere in the pattern, the search
||| window can shift so that the pattern starts immediately after the
||| mismatched byte, resulting in a default shift of 1.
|||
||| This table is typically used in Boyer–Moore–style pattern matching
||| algorithms to determine optimal skip distances after mismatches.
|||
||| O((length of pattern) + (alphabet size))
export
occurrences :  (bs : ByteString)
            -> F1 s (MArray s 256 Nat)
occurrences bs t =
  case null bs of
    True  =>
      (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.occurrences: empty ByteString") # t
    False =>
      let arr # t := marray1 256 (the Nat 1) t
        in go 0 bs arr t
  where
    go :  (i : Nat)
       -> (bs : ByteString)
       -> (arr : MArray s 256 Nat)
       -> F1 s (MArray s 256 Nat)
    go i bs arr t =
      let patend := minus (length bs) 1
        in case i == patend of
             True  =>
               arr # t
             False =>
               let i' := index i bs
                 in case i' of
                      Nothing  =>
                        (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.occurrences.go: can't index into ByteString") # t
                      Just i'' =>
                        case tryNatToFin (cast {to=Nat} i'') of
                          Nothing  =>
                            (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.occurrences.go: can't convert Nat to Fin") # t
                          Just i''' =>
                            let () # t := set arr i''' i t
                              in assert_total (go (plus i 1) bs arr t)
