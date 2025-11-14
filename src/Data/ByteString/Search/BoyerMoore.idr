||| Boyer-Moore search of ByteStrings
module Data.ByteString.Search.BoyerMoore

import Data.ByteString.Search.Internal.Utils

import Data.Array.Core
import Data.Array.Mutable
import Data.Bits
import Data.ByteString
import Data.Linear.Ref1
import Data.So

%hide Data.Buffer.Core.get
%hide Data.Buffer.Core.set

%default total

||| Returns a list of starting positions of a pattern `ByteString`
||| (0-based) across a target `ByteString`.
private
matcher :  Bool
        -> ByteString
        -> ByteString
        -> F1 s (List Nat)
matcher overlap pat target t =
  case length pat == S Z of
    True  =>
      let patzero := index Z pat
        in case patzero of
             Nothing       =>
               (assert_total $ idris_crash "Data.ByteString.Search.DFA.matcher: can't index into ByteString") # t
             Just patzero' =>
               let headelem := elemIndex patzero' pat
                 in case headelem of
                      Nothing        =>
                        (assert_total $ idris_crash "Data.ByteString.Search.DFA.matcher: byte does not appear in ByteString") # t
                      Just headelem' =>
                        (headelem' :: []) # t
    False =>
      let dfa    # t := automaton pat t
          match' # t := match Z Z pat target Lin dfa overlap t
        in (match' <>> []) # t
  where
    match :  (state : Nat)
          -> (idx : Nat)
          -> (pat : ByteString)
          -> (target : ByteString)
          -> (final : SnocList Nat)
          -> (dfa : MArray s (mult (plus (length pat) 1) 256) Nat)
          -> (overlap : Bool)
          -> F1 s (SnocList Nat)
    match Z idx pat target final dfa overlap t =
      case idx == length target of
        True  =>
          final # t
        False =>
          let idx' := index idx target
            in case idx' of
                 Nothing    =>
                   (assert_total $ idris_crash "Data.ByteString.Search.DFA.matcher:match: can't index into ByteString") # t
                 Just idx'' =>
                   let patzero := index Z pat
                     in case patzero of
                          Nothing       =>
                            (assert_total $ idris_crash "Data.ByteString.Search.DFA.matcher:match: can't index into ByteString") # t
                          Just patzero' =>
                            case idx'' == patzero' of
                              True  =>
                                assert_total (match (S 0) (S idx) pat target final dfa overlap t)
                              False =>
                                assert_total (match Z (S idx) pat target final dfa overlap t)
    match state idx pat target final dfa overlap t =
      case idx == length target of
        True  =>
          final # t
        False =>  
          let idx' := index idx target
            in case idx' of
                 Nothing    =>
                   (assert_total $ idris_crash "Data.ByteString.Search.DFA.matcher:match: can't index into ByteString") # t
                 Just idx'' =>
                   let nstateidx := plus (mult state 256) (cast {to=Nat} idx'')
                     in case tryNatToFin nstateidx of
                          Nothing         =>
                            (assert_total $ idris_crash "Data.ByteString.Search.DFA.matcher:match: can't convert Nat to Fin") # t
                          Just nstateidx' =>
                            let nstate # t := get dfa nstateidx' t
                                nxtidx     := S idx
                              in case nstate == length pat of
                                   True  =>
                                     let final'  := minus nxtidx (length pat)
                                         final'' := final :< final'
                                       in case overlap of
                                            True  =>
                                              let ams := S (minus nxtidx (length pat))
                                                in assert_total (match Z ams pat target final'' dfa overlap t)
                                            False =>
                                              assert_total (match Z nxtidx pat target final'' dfa overlap t)
                                   False =>
                                     assert_total (match nstate nxtidx pat target final dfa overlap t)

||| Performs a string search on a `ByteString` utilizing a determinisitic-finite-automaton (DFA).
|||
||| This function finds all (0-based) starting indices of the non-empty pattern `ByteString`
||| pat within the non-empty target `ByteString`, using the deterministic-finite-automaton
||| (DFA) computed by `automaton`.
|||
||| Example:
|||
||| | pat  | target     |
||| | ---- | ---------- |
||| | "AN" | "ANPANMAN" |
|||
||| | Start | Substring      | Match? | Explanation                                      |
||| | ----- | -------------- | ------ | ------------------------------------------------ |
||| | 0     | **"AN"**PANMAN | Yes    | Full pattern `"AN"` matches starting at index 0. |
||| | 1     | A**"NP"**ANMAN | No     | Mismatch after the first character.              |
||| | 2     | AN**"PA"**NMAN | No     | No match — next candidate after suffix shift.    |
||| | 3     | ANP**"AN"**MAN | Yes    | Match found at index 3.                          |
||| | 4     | ANPA**"NM"**AN | No     | Mismatch.                                        |
||| | 5     | ANPAN**"MA"**N | No     | Mismatch.                                        |
||| | 6     | ANPANM**"AN"** | Yes    | Final match found at index 6.                    |
||| 
|||
||| matchDFA "AN" "ANPANMAN" => [0, 3, 6]
|||
export
matchDFA :  (pat : ByteString)
         -> (target : ByteString)
         -> {0 prfpat : So (not $ null pat)}
         -> {0 prftarget : So (not $ null target)}
         -> F1 s (List Nat)
matchDFA pat target {prfpat} {prftarget} t =
  matcher False pat target t

||| Performs a string search on a `ByteString` utilizing a determinisitic-finite-automaton (DFA).
|||
||| This function finds all (0-based) indices (possibly overlapping)
||| of the non-empty pattern `ByteString` pat
||| within the non-empty target `ByteString`, using the deterministic-finite-automaton
||| (DFA) computed by `automaton`.
|||
||| Example:
|||
||| | pat   | target      |
||| | ----- | ----------- |
||| | "ABC" | "ABCABCABC" |
|||
||| | Start | Substring       | Match? | Explanation                                                      |
||| | ----- | --------------- | ------ | ---------------------------------------------------------------- |
||| | 0     | **"ABCABC"**ABC | Yes    | Full pattern matches starting at index 0.                        |
||| | 1     | A**"BCABCA"**BC | No     | Mismatch starts immediately after first letter.                  |
||| | 2     | AB**"CABCAA"**C | No     | Shift by suffix table → mismatch on 2nd char.                    |
||| | 3     | ABC**"ABC"**    | Yes    | Overlapping match starting at index 3 (because `"ABC"` repeats). |
||| 
||| indicesDFA "ABCABC" "ABCABCABC" => [0, 3]
|||
export
indicesDFA :  (pat : ByteString)
           -> (target : ByteString)
           -> {0 prfpat : So (not $ null pat)}
           -> {0 prftarget : So (not $ null target)}
           -> F1 s (List Nat)
indicesDFA pat target {prfpat} {prftarget} t =
  matcher True pat target t
