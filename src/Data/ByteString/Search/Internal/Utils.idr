||| Utilities for string searching algorithms
module Data.ByteString.Search.Internal.Utils

import Data.Array.Core
import Data.Array.Mutable
import Data.Bits
import Data.ByteString
import Data.Linear.Ref1
import Data.So

%hide Data.Buffer.Core.get
%hide Data.Buffer.Core.set

%default total

--------------------------------------------------------------------------------
--          Preprocessing
--------------------------------------------------------------------------------

||| Computes the suffix-oriented KMP border table for a given pattern.
|||
||| Each entry at index i (0 ≤ i ≤ length pattern) stores the length of the
||| longest proper prefix of the prefix pattern[0..i-1] that is also a
||| suffix. This “border” is used to determine how far to backtrack in
||| pattern matching when a mismatch occurs.
|||
||| Unlike the standard KMP table, this table is suffix-oriented and
||| built in a descending, structurally recursive manner.
|||
||| The table helps efficiently skip positions in the pattern during
||| substring search, while descending from longer prefixes to shorter ones.
|||
||| Example: ANPANMAN"
|||
||| Indices: 0..8
|||
||| Prefixes: ""   "A"   "AN"   "ANP"  "ANPA"  "ANPAN"  "ANPANM"  "ANPANMA"  "ANPANMAN"
||| Borders:  0    0     0      0      1       2        0         1          2
|||
export
kmpBorders :  (bs : ByteString)
           -> F1 s (MArray s (S (length bs)) Nat)
kmpBorders bs t =
  let arr # t := unsafeMArray1 (S (length bs)) t
      ()  # t := go (length bs) bs arr t
    in arr # t
  where
    dec :  (i : Nat)
        -> (j : Nat)
        -> (bs : ByteString)
        -> (arr : MArray s (S (length bs)) Nat)
        -> F1 s Nat
    dec _ Z _  _   t =
      Z # t
    dec i j bs arr t =
      case tryNatToFin j of
        Nothing   =>
          (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.kmpBorders.dec: can't convert Nat to Fin") # t
        Just j' =>
          let j'' # t := get arr j' t
              wj      := index j'' bs
            in case wj of
                 Nothing  =>
                   (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.kmpBorders.dec: can't index into ByteString") # t
                 Just wj' =>
                   let wi := index (minus i 1) bs
                     in case wi of
                          Nothing  =>
                            (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.kmpBorders.dec: can't index into ByteString") # t
                          Just wi' =>
                            case (cast {to=Nat} wi') == (cast {to=Nat} wj') of
                              True  =>
                                plus j'' 1 # t
                              False =>
                                case j'' == 0 of
                                  True  =>
                                    Z # t
                                  False =>
                                    assert_total (dec i j'' bs arr t)
    go :  (i : Nat)
       -> (bs : ByteString)
       -> (arr : MArray s (S (length bs)) Nat)
       -> F1' s
    go Z     _ arr t =
      case tryNatToFin 0 of
        Nothing   =>
          (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.kmpBorders.go: can't convert Nat to Fin") # t
        Just zero =>
          set arr zero 0 t
    go (S i) bs arr t =
      let () # t := assert_total (go i bs arr t)
        in case tryNatToFin (S i) of
             Nothing =>
               (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.kmpBorders.go: can't convert Nat to Fin") # t
             Just i' =>
               let j # t := dec (S i) i bs arr t
                 in set arr i' j t

||| Builds a deterministic finite automaton (DFA) for pattern matching over a `ByteString`.
|||
||| The automaton encodes transitions from (state, input byte) → next state,
||| allowing efficient streaming search for the pattern within input data.
|||
||| It produces a flattened transition table of size `((length pattern) + 1) * 256`,
||| where 256 corresponds to all possible byte values (0–255).
|||
||| States correspond to pattern prefixes:
||| - State 0: no match (empty prefix)
||| - State i: matched the first i bytes of the pattern
||| - State (length pattern): full match
|||
||| Transition behavior is derived from the KMP border table (`kmpBorders`),
||| ensuring correct fallback transitions and eliminating redundant backtracking.
|||
||| Example: "ANPANMAN"
|||
||| These following equation is used to determine the "flat" index to build the automaton:
|||
||| flatindex = (state ∗ alphabetsize) + charcode
|||
||| Where:
|||
||| state : Range from 0 to length of the input pattern
|||
||| alphabetsize : All possible input characters (in this case extended ASCII, 8-bit range from 0 to 255)
|||
||| charcode : Characters are interpreted via its ASCII code ('A' = 65, 'M' = 77, 'N' = 78, 'P' = 80, and so on)
|||
||| | Flat index | State | Char code | Char | Meaning       |
||| | ---------- | ----- | --------- | ---- | ------------- |
||| | 65         | 0     | 65        | 'A'  | δ(0, 'A') = 1 |
||| | 321        | 1     | 65        | 'A'  | δ(1, 'A') = 1 |
||| | 334        | 1     | 78        | 'N'  | δ(1, 'N') = 2 |
||| | 577        | 2     | 65        | 'A'  | δ(2, 'A') = 1 |
||| | 592        | 2     | 80        | 'P'  | δ(2, 'P') = 3 |
||| | 833        | 3     | 65        | 'A'  | δ(3, 'A') = 4 |
||| | 1089       | 4     | 65        | 'A'  | δ(4, 'A') = 1 |
||| | 1102       | 4     | 78        | 'N'  | δ(4, 'N') = 5 |
||| | 1345       | 5     | 65        | 'A'  | δ(5, 'A') = 1 |
||| | 1357       | 5     | 77        | 'M'  | δ(5, 'M') = 6 |
||| | 1601       | 6     | 65        | 'A'  | δ(6, 'A') = 7 |
||| | 1857       | 7     | 65        | 'A'  | δ(7, 'A') = 1 |
||| | 1870       | 7     | 78        | 'N'  | δ(7, 'N') = 8 |
||| | 2113       | 8     | 65        | 'A'  | δ(8, 'A') = 1 |
|||
export
automaton :  (bs : ByteString)
          -> F1 s (MArray s (mult (plus (length bs) 1) 256) Nat)
automaton bs t =
  let arr  # t := unsafeMArray1 (mult (plus (length bs) 1) 256) t
      bord # t := kmpBorders bs t
      ()   # t := go Z bs arr bord t
    in arr # t
  where
    flattenIndex :  (st : Nat)
                 -> (byte : Nat)
                 -> (bs : ByteString)
                 -> (arr : MArray s (mult (plus (length bs) 1) 256) Nat)
                 -> F1 s (Fin (mult (plus (length bs) 1) 256))
    flattenIndex st byte bs arr t =
      let idx := plus (mult st 256) byte
        in case tryNatToFin idx of
             Nothing   =>
               (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.automaton.loop: can't convert Nat to Fin") # t
             Just idx' =>
               idx' # t
    loop :  (b : Nat)
         -> (cur : Nat)
         -> (patbyte : Maybe Bits8)
         -> (bordcur : Nat)
         -> (bs : ByteString)
         -> (arr : MArray s (mult (plus (length bs) 1) 256) Nat)
         -> F1' s
    loop Z     cur patbyte bordcur bs arr t =
      let idx # t := flattenIndex cur Z bs arr t
        in case patbyte of
             Nothing       =>
               case cur == Z of
                 True  =>
                   set arr idx Z t
                 False =>
                   let fidx     # t := flattenIndex bordcur Z bs arr t
                       bordcur' # t := get arr fidx t
                     in set arr idx bordcur' t
             Just patbyte' =>
               case Z == (cast {to=Nat} patbyte') of
                 True  =>
                   set arr idx (S cur) t
                 False =>
                   case cur == Z of
                     True  =>
                       set arr idx Z t
                     False =>
                       let fidx     # t := flattenIndex bordcur Z bs arr t
                           bordcur' # t := get arr fidx t
                         in set arr idx bordcur' t
    loop (S b) cur patbyte bordcur bs arr t =
      let idx # t := flattenIndex cur (S b) bs arr t
        in case patbyte of
             Nothing       =>
               case cur == Z of
                 True  =>
                   let () # t := set arr idx Z t
                     in assert_total (loop b cur patbyte bordcur bs arr t)
                 False =>
                   let fidx     # t := flattenIndex bordcur (S b) bs arr t
                       bordcur' # t := get arr fidx t
                       ()       # t := set arr idx bordcur' t
                     in assert_total (loop b cur patbyte bordcur' bs arr t)
             Just patbyte' =>
               case (S b) == (cast {to=Nat} patbyte') of
                 True  =>
                   let () # t := set arr idx (S cur) t
                     in assert_total (loop b cur patbyte bordcur bs arr t)
                 False =>
                   case cur == Z of
                     True  =>
                       let () # t := set arr idx Z t
                         in assert_total (loop b cur patbyte bordcur bs arr t)
                     False =>
                       let fidx     # t := flattenIndex bordcur (S b) bs arr t
                           bordcur' # t := get arr fidx t
                           ()       # t := set arr idx bordcur' t
                         in assert_total (loop b cur patbyte bordcur' bs arr t)
    fillState :  (cur : Nat)
              -> (bs : ByteString)
              -> (arr : MArray s (mult (plus (length bs) 1) 256) Nat)
              -> (bord : MArray s (S (length bs)) Nat)
              -> F1' s
    fillState cur bs arr bord t =
      case tryNatToFin cur of
        Nothing   =>
          (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.automaton.fillState: can't convert Nat to Fin") # t
        Just cur' =>
          let bordcur # t := get bord cur' t
              patbyte     := index cur bs
            in loop 255 cur patbyte bordcur bs arr t
    go :  (state : Nat)
       -> (bs : ByteString)
       -> (arr : MArray s (mult (plus (length bs) 1) 256) Nat)
       -> (bord : MArray s (S (length bs)) Nat)
       -> F1' s
    go state bs arr bord t =
      case state > (length bs) of
        True  =>
          () # t
        False =>
          let () # t := fillState state bs arr bord t
            in assert_total (go (S state) bs arr bord t)

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
||| (position in pattern) - (last occurrence of b in initial pattern)
|||
||| If the byte b does not appear anywhere in the pattern, the search
||| window can shift so that the pattern starts immediately after the
||| mismatched byte, resulting in a default shift of 1.
|||
||| This table is typically used in Boyer–Moore–style pattern matching
||| algorithms to determine optimal skip distances after mismatches.
|||
||| O((length of pattern) + (alphabet size))
|||
||| Example: "ANPANMAN"
|||
||| | Flat index / ASCII | char | value |
||| | ------------------ | ---- | ----- |
||| |        65          | 'A'  |    -6 |
||| |        77          | 'M'  |    -5 |
||| |        78          | 'N'  |    -4 |
||| |        80          | 'P'  |    -2 |
|||
export
occurrences :  (bs : ByteString)
            -> {0 prf : So (not $ null bs)}
            -> F1 s (MArray s 256 Int)
occurrences bs t =
  let arr # t := marray1 256 (the Int 1) t
      ()  # t := go Z (length bs) bs arr t
    in arr # t
  where
    go :  (i : Nat)
       -> (patend : Nat)
       -> (bs : ByteString)
       -> (arr : MArray s 256 Int)
       -> F1' s
    go i patend bs arr t =
      case (S i) >= patend of
        True  =>
          () # t
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
                       let () # t := set arr i''' (negate $ cast {to=Int} i) t
                         in assert_total (go (plus i 1) patend bs arr t)

||| Builds the table of suffix lengths for the given pattern.
|||
||| The value at index `i` is the length of the longest common suffix
||| between the entire pattern and the prefix of the pattern ending at `i`.
|||
||| Typically, most entries are 0. Only when the byte at position `i`
||| matches the final byte of the pattern can the value be positive.
|||
||| The final entry (at `patEnd`) equals the pattern length, since the
||| pattern is identical to itself. In general, `0 <= ar[i] <= i + 1`.
|||
||| To ensure linear preprocessing, the algorithm avoids the naive
||| quadratic approach by reusing information from previously identified
||| suffixes.
|||
||| When the current index lies within an already known suffix, we align
||| that suffix with the end of the pattern and check whether it extends
||| beyond the current position. If so, we reuse the stored suffix length;
||| otherwise, we extend the suffix explicitly.
|||
||| If the current index lies outside any known suffix, we compare against
||| the final byte of the pattern. If this yields a suffix of length > 1,
||| we enter the “known suffix” case for subsequent indices; otherwise,
||| we continue scanning normally.
|||
||| Example : "ANPANMAN"
|||
||| Raw suffix-lengths array used to compute the good suffix shift table
|||
||| | i | pat[i] | matches pattern end? | diff | nextI | prevI | ar[i] |
||| | - | ------ | -------------------- | ---- | ----- | ----- | ----- |
||| | 0 | A      | No                   | -    | -     | -     | 0     |
||| | 1 | N      | Yes                  | 6    | 0     | 0     | 1     |
||| | 2 | P      | No                   | -    | -     | -     | 0     |
||| | 3 | A      | No                   | -    | -     | -     | 0     |
||| | 4 | N      | Yes                  | 3    | 3     | 3     | 1     |
||| | 5 | M      | No                   | -    | -     | -     | 0     |
||| | 6 | A      | No                   | -    | -     | -     | 0     |
||| | 7 | N      | -                    | -    | -     | -     | 8     |
|||
export
suffixLengths :  (bs : ByteString)
              -> {0 prf : So (not $ null bs)}
              -> F1 s (MArray s (length bs) Nat)
suffixLengths bs t =
  let arr # t := marray1 (length bs) (the Nat 0) t
    in case tryNatToFin (minus (length bs) 1) of
         Nothing  =>
           (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths: can't convert Nat to Fin") # t
         Just idx =>
           let () # t := set arr idx (length bs) t
               () # t := noSuffix (minus (length bs) 2) bs arr t
             in arr # t
  where
    dec :  (diff : Nat)
        -> (j : Nat)
        -> F1 s Nat
    dec diff j t =
      case j == Z of
        True  =>
          j # t
        False =>
          let j'  := index j bs
            in case j' of
                 Nothing  =>
                   (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.dec: can't index into ByteString") # t
                 Just j'' =>
                   let j''' := index (plus j diff) bs
                     in case j''' of
                          Nothing    =>
                            (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.dec: can't index into ByteString") # t
                          Just j'''' =>
                            case j'' /= j'''' of
                              True  =>
                                j # t
                              False =>
                                assert_total (dec diff (minus j 1) t)
    mutual
      suffixLoop :  (pre : Nat)
                 -> (end : Nat)
                 -> (idx : Nat)
                 -> (bs : ByteString)
                 -> (arr : MArray s (length bs) Nat)
                 -> F1' s
      suffixLoop _   _   Z       _  _   t =
        () # t
      suffixLoop pre end (S idx) bs arr t =
        case pre < (S idx) of
          True  =>
            let idx'  := index (S idx) bs
              in case idx' of
                   Nothing    =>
                     (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.suffixLoop: can't index into ByteString") # t
                   Just idx'' =>
                     let idx''' := index (minus (length bs) 1) bs
                       in case idx''' of
                            Nothing      =>
                              (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.suffixLoop: can't index into ByteString") # t
                            Just idx'''' =>
                              case idx'' /= idx'''' of
                                True  =>
                                  case tryNatToFin (S idx) of
                                    Nothing   =>
                                      (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.suffixLoop: can't convert Nat to Fin") # t
                                    Just idxs =>
                                      let () # t := set arr idxs 0 t
                                        in assert_total (suffixLoop pre (minus end 1) idx bs arr t)
                                False =>
                                  case tryNatToFin end of
                                    Nothing   =>
                                      (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.suffixLoop: can't convert Nat to Fin") # t
                                    Just end' =>
                                      let prevs # t := get arr end' t
                                        in case tryNatToFin (S idx) of
                                             Nothing   =>
                                               (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.suffixLoop: can't convert Nat to Fin") # t
                                             Just idxs =>
                                               case (plus pre prevs) < (S idx) of
                                                 True  =>
                                                   let () # t := set arr idxs prevs t
                                                     in assert_total (suffixLoop pre (minus end 1) idx bs arr t)
                                                 False =>
                                                   let pri # t := dec (minus (length bs) (S idx)) pre t
                                                       ()  # t := set arr idxs (minus (S idx) pri) t
                                                     in assert_total (suffixLoop pri (minus (length bs) 2) idx bs arr t)
          False =>
            noSuffix (S idx) bs arr t
      noSuffix :  (i : Nat)
               -> (bs : ByteString)
               -> (arr : MArray s (length bs) Nat)
               -> F1' s
      noSuffix Z     _  _   t =
        () # t
      noSuffix (S i) bs arr t =
        let patati := index i bs
          in case patati of
               Nothing  =>
                 (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.noSuffix: can't index into ByteString") # t
               Just patati' =>
                 let patatend := index (minus (length bs) 1) bs
                   in case patatend of
                        Nothing        =>
                          (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.noSuffix: can't index into ByteString") # t
                        Just patatend' => 
                          case patati' == patatend' of
                            True  =>
                              let diff      := minus (length bs) i
                                  nexti     := minus i 1
                                  previ # t := dec diff nexti t
                                in case tryNatToFin i of
                                     Nothing =>
                                       (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.noSuffix: can't convert Nat to Fin") # t
                                     Just i' =>
                                       case previ == nexti of
                                         True  =>
                                           let () # t := set arr i' 1 t
                                             in assert_total (noSuffix nexti bs arr t)
                                         False =>
                                           let () # t := set arr i' (minus i previ) t
                                             in assert_total (suffixLoop previ (minus (length bs) 2) nexti bs arr t)
                            False =>
                              case tryNatToFin i of
                                Nothing =>
                                  (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.noSuffix: can't convert Nat to Fin") # t
                                Just i' =>
                                  let () # t := set arr i' 0 t
                                    in assert_total (noSuffix i bs arr t)

||| Table of suffix-shifts
|||
||| When a mismatch occurs at pattern position patpos, assumed to be not the
||| last position in the pattern, the suffix u of length (patend - patpos)
||| has been successfully matched.
||| Let c be the byte in the pattern at position patpos.
|||
||| If the sub-pattern u also occurs in the pattern somewhere *not* preceded
||| by c, let upos be the position of the last byte in u for the last of
||| all such occurrences. Then there can be no match if the window is shifted
||| less than (patend - upos) places, because either the part of the string
||| which matched the suffix u is not aligned with an occurrence of u in the
||| pattern, or it is aligned with an occurrence of u which is preceded by
||| the same byte c as the originally matched suffix.
|||
||| If the complete sub-pattern u does not occur again in the pattern, or all
||| of its occurrences are preceded by the byte c, then we can align the
||| pattern with the string so that a suffix v of u matches a prefix of the
||| pattern. If v is chosen maximal, no smaller shift can give a match, so
||| we can shift by at least (patlen - length v).
|||
||| If a complete match is encountered, we can shift by at least the same
||| amount as if the first byte of the pattern was a mismatch, no complete
||| match is possible between these positions.
|||
||| For non-periodic patterns, only very short suffixes will usually occur
||| again in the pattern, so if a longer suffix has been matched before a
||| mismatch, the window can then be shifted entirely past the partial
||| match, so that part of the string will not be re-compared.
||| For periodic patterns, the suffix shifts will be shorter in general,
||| leading to an O(strlen * patlen) worst-case performance.
|||
||| To compute the suffix-shifts, we use an array containing the lengths of
||| the longest common suffixes of the entire pattern and its prefix ending
||| with position pos.
|||
||| Example: "ANPANMAN"
|||
||| | idx | suff[idx] | target = 7 - suff[idx] | value = 7 - idx | arr after write   | Notes                      |
||| | --- | --------- | ---------------------- | --------------- | ----------------- | -------------------------- |
||| | 0   | 1         | 6                      | 7               | [8,8,8,8,8,8,7,8] | arr[6] updated             |
||| | 1   | 1         | 6                      | 6               | [8,8,8,8,8,8,6,8] | arr[6] overwritten         |
||| | 2   | 1         | 6                      | 5               | [8,8,8,8,8,8,5,8] | arr[6] overwritten         |
||| | 3   | 1         | 6                      | 4               | [8,8,8,8,8,8,4,8] | arr[6] overwritten         |
||| | 4   | 1         | 6                      | 3               | [8,8,8,8,8,8,3,8] | arr[6] overwritten         |
||| | 5   | 1         | 6                      | 2               | [8,8,8,8,8,8,2,8] | arr[6] overwritten         |
||| | 6   | 3         | 4                      | 1               | [8,8,8,8,8,8,3,1] | arr[4] updated, arr[7] = 1 |
|||
export
suffixShifts :  (bs : ByteString)
             -> {0 prf : So (not $ null bs)}
             -> F1 s (MArray s (length bs) Nat)
suffixShifts bs {prf} t =
  let arr  # t := marray1 (length bs) (length bs) t
      suff # t := suffixLengths bs {prf=prf} t
      ()   # t := prefixShift (minus (length bs) 2) Z bs suff arr t
      ()   # t := suffixShift Z bs suff arr t
    in arr # t
  where
    fillToShift :  (i : Nat)
                -> (shift : Nat)
                -> (bs : ByteString)
                -> (arr : MArray s (length bs) Nat)
                -> F1' s
    fillToShift i shift bs arr t =
      case i == shift of
        True =>
          () # t
        False =>
          case tryNatToFin i of
            Nothing =>
              (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixShifts.fillToShift: can't convert Nat to Fin") # t
            Just i' =>
              let () # t := set arr i' shift t
                in assert_total (fillToShift (plus i 1) shift bs arr t)
    prefixShift :  (idx : Nat)
                -> (j : Nat)
                -> (bs : ByteString)
                -> (suff : MArray s (length bs) Nat)
                -> (arr : MArray s (length bs) Nat)
                -> F1' s
    prefixShift Z       _ _  _    _   t =
      () # t
    prefixShift (S idx) j bs suff arr t =
      case tryNatToFin (S idx) of
        Nothing   =>
          (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixShifts.prefixShift: can't convert Nat to Fin") # t
        Just idx' =>
          let idx'' # t := get suff idx' t
            in case idx'' == (S (S idx)) of
                 True =>
                   let shift  := minus (length bs) (S idx)
                       () # t := fillToShift j shift bs arr t
                     in assert_total (prefixShift idx shift bs suff arr t)                                      
                 False =>
                   assert_total (prefixShift idx j bs suff arr t)
    suffixShift :  (idx : Nat)
                -> (bs : ByteString)
                -> (suff : MArray s (length bs) Nat)
                -> (arr : MArray s (length bs) Nat)
                -> F1' s
    suffixShift idx bs suff arr t =
      let patend := minus (length bs) 1
        in case idx > patend of
             True  =>
               () # t
             False =>
               case idx == patend of
                 True  =>
                   () # t
                 False =>
                   case tryNatToFin idx of
                     Nothing   =>
                       (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixShifts.suffixShift: can't convert Nat to Fin") # t
                     Just idx' =>
                       let idx'' # t := get suff idx' t
                           patend'   := minus (length bs) 1
                           target    := minus patend' idx''
                         in case tryNatToFin target of
                              Nothing      =>
                                (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixShifts.suffixShift: can't convert Nat to Fin") # t
                              Just target' =>
                                let value  := minus patend' idx
                                    () # t := set arr target' value t
                                  in assert_total (suffixShift (plus idx 1) bs suff arr t)
