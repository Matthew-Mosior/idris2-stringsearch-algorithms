||| Utilities for string searching algorithms
module Data.ByteString.Search.Internal.Utils

import Data.Array.Core
import Data.Array.Mutable
import Data.ByteString
import Data.Linear.Ref1

%hide Data.Buffer.Core.get
%hide Data.Buffer.Core.set

%default total

||| Calculates the width of the widest borders of the
||| prefixes of the pattern which are not extensible
||| to the borders of the next longest prefix.
||| Most entries will be 0.
export
kmpBorders :  (bs : ByteString)
           -> F1 s (MArray s (length bs) Nat)
kmpBorders bs t =
  let arr # t := unsafeMArray1 (length bs) t
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

{-
||| A deterministic finite automaton (DFA) is constructed based on the pattern to be searched.
||| Each state in the automaton represents a prefix of the pattern that has been successfully matched so far.
||| Transitions between states occur based on the input characters from the text.
export
automaton :  ByteString
          -> F1 s (MArray s n Nat)
automaton bs t =
  let patlen := length bs-}    
