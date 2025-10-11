||| Utilities for string searching algorithms
module Data.ByteString.Search.Internal.Utils

import Data.Array.Core
import Data.Array.Mutable
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
||| represents a flattened transition table of size `(pattern length + 1) * 256`,
||| where 256 corresponds to the number of possible byte values (0–255).
|||
||| Each state represents a prefix of the pattern:
||| - State 0: empty prefix
||| - State i: matched the first i bytes of the pattern
||| - Final state = pattern length: full match
|||
||| Transitions are initialized using the KMP border table, generated via `kmpBorders`,
||| to ensure correct failure transitions, avoiding redundant backtracking.
export
automaton :  ByteString
          -> F1 s (MArray s n Nat)
automaton bs t =
  let arr # t := unsafeMArray1 (minus (mult (plus (length bs) 1) 256) 1) t
    in case tryNatToFin 0 of
         Nothing   =>
           (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.kmpBorders: can't convert Nat to Fin") # t
         Just zero =>
           let () # t := set arr zero 1 t
             in go 1 0 bs arr t
