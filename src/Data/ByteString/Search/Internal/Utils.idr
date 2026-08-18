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
           -> F1 s (Maybe (MArray s (S (length bs)) Nat))
kmpBorders bs t =
  let arr  # t := unsafeMArray1 (S (length bs)) t
      arr' # t := go (length bs) bs arr t
    in arr' # t
  where
    dec :  (i : Nat)
        -> (j : Nat)
        -> (bs : ByteString)
        -> (arr : MArray s (S (length bs)) Nat)
        -> F1 s (Maybe Nat)
    dec _ Z _  _   t =
      Just Z # t
    dec i j bs arr t =
      let Just j'  := tryNatToFin j
            | Nothing => Nothing # t 
          j'' # t  := get arr j' t
          wj       := index j'' bs
          Just wj' := wj
            | Nothing => Nothing # t
          wi       := index (minus i 1) bs
          Just wi' := wi
            | Nothing => Nothing # t
          False    := (cast {to=Nat} wi') == (cast {to=Nat} wj')
            | True => Just (plus j'' 1) # t
          False    := j'' == 0
            | True => Just Z # t
        in assert_total (dec i j'' bs arr t)
    go :  (i : Nat)
       -> (bs : ByteString)
       -> (arr : MArray s (S (length bs)) Nat)
       -> F1 s (Maybe (MArray s (S (length bs)) Nat))
    go Z     _ arr t =
      let Just zero := tryNatToFin 0
            | Nothing => Nothing # t
          ()    # t := set arr zero 0 t
        in Just arr # t
    go (S i) bs arr t =
      let i'   # t := assert_total (go i bs arr t)
          Just   _ := i'
            | Nothing => Nothing # t
          Just i'' := tryNatToFin (S i)
            | Nothing => Nothing # t
          j    # t := dec (S i) i bs arr t
          Just j' := j
            | Nothing => Nothing # t
          ()   # t := set arr i'' j' t
        in Just arr # t

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
||| - state : Range from 0 to length of the input pattern
||| - alphabetsize : All possible input characters (in this case extended ASCII, 8-bit range from 0 to 255)
||| - charcode : Characters are interpreted via its ASCII code ('A' = 65, 'M' = 77, 'N' = 78, 'P' = 80, and so on)
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
          -> F1 s (Maybe (MArray s (mult (plus (length bs) 1) 256) Nat))
automaton bs t =
  let arr    # t := unsafeMArray1 (mult (plus (length bs) 1) 256) t
      bord   # t := kmpBorders bs t
      Just bord' := bord
        | Nothing => Nothing # t
      arr'   # t := go Z bs arr bord' t
      Just arr'' := arr'
        | Nothing => Nothing # t
    in Just arr'' # t 
  where
    flattenIndex :  (st : Nat)
                 -> (byte : Nat)
                 -> (bs : ByteString)
                 -> (arr : MArray s (mult (plus (length bs) 1) 256) Nat)
                 -> F1 s (Maybe (Fin (mult (plus (length bs) 1) 256)))
    flattenIndex st byte bs arr t =
      let idx := plus (mult st 256) byte
          Just idx' := tryNatToFin idx
            | Nothing => Nothing # t
        in Just idx' # t
    loop :  (b : Nat)
         -> (cur : Nat)
         -> (patbyte : Maybe Bits8)
         -> (bordcur : Nat)
         -> (bs : ByteString)
         -> (arr : MArray s (mult (plus (length bs) 1) 256) Nat)
         -> F1 s (Maybe (MArray s (mult (plus (length bs) 1) 256) Nat))
    loop Z     cur patbyte bordcur bs arr t =
      let idx       # t := flattenIndex cur Z bs arr t
          Just idx'     := idx
            | Nothing => Nothing # t
          Just patbyte' := patbyte
            | Nothing =>
                let False := cur == Z
                      | True =>
                          let () # t := set arr idx' Z t
                            in Just arr # t
                    fidx # t := flattenIndex bordcur Z bs arr t
                    Just fidx' := fidx
                      | Nothing =>
                          Nothing # t
                    bordcur' # t := get arr fidx' t
                    ()       # t := set arr idx' bordcur' t
                  in Just arr # t
          False         := Z == (cast {to=Nat} patbyte')
            | True =>
                let () # t := set arr idx' (S cur) t
                  in Just arr # t
          False         := cur == Z
            | True =>
                let () # t := set arr idx' Z t
                  in Just arr # t
          fidx # t      := flattenIndex bordcur Z bs arr t
          Just fidx'    := fidx
            | Nothing =>
                Nothing # t
          bordcur' # t  := get arr fidx' t
          ()       # t  := set arr idx' bordcur' t
            in Just arr # t
    loop (S b) cur patbyte bordcur bs arr t =
      let idx       # t := flattenIndex cur (S b) bs arr t
          Just idx'     := idx
            | Nothing => Nothing # t
          Just patbyte' := patbyte
            | Nothing =>
                let False := cur == Z
                      | True =>
                          let () # t := set arr idx' Z t
                            in loop b cur patbyte bordcur bs arr t
                    fidx # t := flattenIndex bordcur (S b) bs arr t
                    Just fidx' := fidx
                      | Nothing =>
                          Nothing # t
                    bordcur' # t := get arr fidx' t
                    ()       # t := set arr idx' bordcur' t
                  in loop b cur patbyte bordcur' bs arr t
          False         := (S b) == (cast {to=Nat} patbyte')
            | True =>
                let () # t := set arr idx' (S cur) t
                  in loop b cur patbyte bordcur bs arr t
          False         := cur == Z
            | True =>
                let () # t := set arr idx' Z t
                  in loop b cur patbyte bordcur bs arr t
          fidx # t      := flattenIndex bordcur (S b) bs arr t
          Just fidx'    := fidx
            | Nothing =>
                Nothing # t
          bordcur' # t  := get arr fidx' t
          ()       # t  := set arr idx' bordcur' t
            in loop b cur patbyte bordcur' bs arr t
    fillState :  (cur : Nat)
              -> (bs : ByteString)
              -> (arr : MArray s (mult (plus (length bs) 1) 256) Nat)
              -> (bord : MArray s (S (length bs)) Nat)
              -> F1 s (Maybe (MArray s (mult (plus (length bs) 1) 256) Nat))
    fillState cur bs arr bord t =
      let Just cur' := tryNatToFin cur
            | Nothing =>
                Nothing # t
          bordcur # t := get bord cur' t
          patbyte     := index cur bs
          arr'    # t := loop 255 cur patbyte bordcur bs arr t
          Just arr'' := arr'
            | Nothing =>
                Nothing # t
        in Just arr'' # t 
    go :  (state : Nat)
       -> (bs : ByteString)
       -> (arr : MArray s (mult (plus (length bs) 1) 256) Nat)
       -> (bord : MArray s (S (length bs)) Nat)
       -> F1 s (Maybe (MArray s (mult (plus (length bs) 1) 256) Nat))
    go state bs arr bord t =
      let False    := state > (length bs)
            | True =>
                Just arr # t
          arr' # t := fillState state bs arr bord t
          Just arr'' := arr'
            | Nothing =>
                Nothing # t
        in assert_total (go (S state) bs arr'' bord t)

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
            -> F1 s (Maybe (MArray s 256 Int))
occurrences bs t =
  let arr  # t := marray1 256 (the Int 1) t
      arr' # t := go Z (length bs) bs arr t
      Just arr'' := arr'
        | Nothing =>
            Nothing # t
    in Just arr'' # t
  where
    go :  (i : Nat)
       -> (patend : Nat)
       -> (bs : ByteString)
       -> (arr : MArray s 256 Int)
       -> F1 s (Maybe (MArray s 256 Int))
    go i patend bs arr t =
      let False     := (S i) >= patend
            | True =>
                Just arr # t
          i'        := index i bs
          Just i''  := i'
            | Nothing =>
                Nothing # t
          Just i''' := tryNatToFin (cast {to=Nat} i'')
            | Nothing =>
                Nothing # t
          ()    # t := set arr i''' (negate $ cast {to=Int} i) t
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
||| | i | pat[i] | matches pattern end? | diff = patEnd - i | nextI = i-1 | prevI (dec diff nextI) | ar[i] |
||| | - | ------ | -------------------- | ----------------- | ----------- | ---------------------- | ----- |
||| | 0 |    A   |          No          |         -         |      -      |            -           |   0   |
||| | 1 |    N   |          Yes         |         6         |      0      |           -1           |   2   |
||| | 2 |    P   |          No          |         -         |      -      |            -           |   0   |
||| | 3 |    A   |          No          |         -         |      -      |            -           |   0   |
||| | 4 |    N   |          Yes         |         3         |      3      |            2           |   2   |
||| | 5 |    M   |          No          |         -         |      -      |            -           |   0   |
||| | 6 |    A   |          No          |         -         |      -      |            -           |   0   |
||| | 7 |    N   |          -           |         -         |      -      |            -           |   8   |
|||
export
suffixLengths :  (bs : ByteString)
              -> {0 prf : So (not $ null bs)}
              -> F1 s (Maybe (MArray s (length bs) Int))
suffixLengths bs t =
  let arr    # t := marray1 (length bs) (the Int 0) t
      Just idx   := tryNatToFin (minus (length bs) 1)
        | Nothing =>
            Nothing # t
      ()     # t := set arr idx (cast {to=Int} (length bs)) t
      arr'   # t := noSuffix (cast {to=Int} (minus (length bs) 2)) bs arr t
      Just arr'' := arr'
        | Nothing =>
            Nothing # t
    in Just arr'' # t
  where
    dec :  (diff : Int)
        -> (j : Int)
        -> F1 s (Maybe Int)
    dec diff j t =
      let False      := j < 0
            | True =>
                Just j # t
          j'         := index (cast {to=Nat} j) bs
          Just j''   := j'
            | Nothing =>
                Nothing # t
          j'''       := index (cast {to=Nat} (j + diff)) bs
          Just j'''' := j'''
            | Nothing =>
                Nothing # t
          False      := j'' /= j''''
            | True =>
                Just j # t
        in assert_total (dec diff (j - 1) t)
    mutual
      suffixLoop :  (pre : Int)
                 -> (end : Int)
                 -> (idx : Int)
                 -> (bs : ByteString)
                 -> (arr : MArray s (length bs) Int)
                 -> F1 s (Maybe (MArray s (length bs) Int))
      suffixLoop _   _   0   _  arr t =
        Just arr # t
      suffixLoop pre end idx bs arr t =
        let True         := pre < idx
              | False =>
                  noSuffix idx bs arr t
            idx'         := index (cast {to=Nat} idx) bs
            Just idx''   := idx'
              | Nothing =>
                  Nothing # t
            idx'''       := index (minus (length bs) 1) bs
            Just idx'''' := idx'''
              | Nothing =>
                  Nothing # t
            False        := idx'' /= idx''''
              | True =>
                  let Just idxs := tryNatToFin (cast {to=Nat} idx)
                        | Nothing =>
                            Nothing # t
                      ()    # t := set arr idxs 0 t
                    in assert_total (suffixLoop pre (end - 1) (idx - 1) bs arr t)
            Just end'    := tryNatToFin (cast {to=Nat} end)
              | Nothing =>
                  Nothing # t
            prevs    # t := get arr end' t
            Just idxs    := tryNatToFin (cast {to=Nat} idx)
              | Nothing =>
                  Nothing # t
            False        := (pre + prevs) < idx
              | True =>
                  let () # t := set arr idxs prevs t
                    in assert_total (suffixLoop pre (end - 1) (idx - 1) bs arr t)
            pri      # t := dec (cast {to=Int} (minus (length bs) (cast {to=Nat} idx))) pre t
            Just pri'    := pri
              | Nothing =>
                  Nothing # t
            ()       # t := set arr idxs (idx - pri') t
          in assert_total (suffixLoop pri' (cast {to=Int} (minus (length bs) 2)) (idx - 1) bs arr t)
      noSuffix :  (i : Int)
               -> (bs : ByteString)
               -> (arr : MArray s (length bs) Int)
               -> F1 s (Maybe (MArray s (length bs) Int))
      noSuffix 0 _  arr t =
        Just arr # t
      noSuffix i bs arr t =
        let patati         := index (cast {to=Nat} i) bs
            Just patati'   := patati
              | Nothing =>
                  Nothing # t
            patatend       := index (minus (length bs) 1) bs
            Just patatend' := patatend
              | Nothing =>
                  Nothing # t
            True           := patati' == patatend'
              | False =>
                  let Just i' := tryNatToFin (cast {to=Nat} i)
                        | Nothing =>
                            Nothing # t
                      ()  # t := set arr i' 0 t
                    in assert_total (noSuffix (i - 1) bs arr t)
            diff           := (cast {to=Int} (minus (length bs) 1)) - i
            nexti          := i - 1
            previ      # t := dec diff nexti t
            Just previ'    := previ
              | Nothing =>
                  Nothing # t
            Just i'        := tryNatToFin (cast {to=Nat} i)
              | Nothing =>
                  Nothing # t
            False          := previ' == nexti
              | True =>
                  let () # t := set arr i' 1 t
                    in assert_total (noSuffix nexti bs arr t)
            ()         # t := set arr i' (i - previ') t
          in assert_total (suffixLoop previ' (cast {to=Int} (minus (length bs) 2)) nexti bs arr t)

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
||| | idx | suff[idx] | target = patEnd - suff[idx] | value = patEnd - idx |    ar after write |
||| | --- | --------- | --------------------------- | -------------------- | ----------------- |
||| |   0 |         0 |                   7 - 0 = 7 |            7 - 0 = 7 | [6,6,6,6,6,6,8,7] |
||| |   1 |         2 |                   7 - 2 = 5 |            7 - 1 = 6 | [6,6,6,6,6,6,8,7] |
||| |   2 |         0 |                           7 |            7 - 2 = 5 | [6,6,6,6,6,6,8,5] |
||| |   3 |         0 |                           7 |            7 - 3 = 4 | [6,6,6,6,6,6,8,4] |
||| |   4 |         2 |                   7 - 2 = 5 |            7 - 4 = 3 | [6,6,6,6,6,3,8,4] |
||| |   5 |         0 |                           7 |            7 - 5 = 2 | [6,6,6,6,6,3,8,2] |
||| |   6 |         0 |                           7 |            7 - 6 = 1 | [6,6,6,6,6,3,8,1] |
|||
export
suffixShifts :  (bs : ByteString)
             -> {0 prf : So (not $ null bs)}
             -> F1 s (Maybe (MArray s (length bs) Int))
suffixShifts bs {prf} t =
  let arr      # t := marray1 (length bs) (cast {to=Int} (length bs)) t
      suff     # t := suffixLengths bs {prf=prf} t
      Just suff'   := suff
        | Nothing =>
            Nothing # t
      arr'     # t := prefixShift (cast {to=Int} (minus (length bs) 2)) 0 bs suff' arr t
      Just arr''   := arr'
        | Nothing =>
            Nothing # t
      arr'''   # t := suffixShift 0 bs suff' arr'' t
      Just arr'''' := arr'''
        | Nothing =>
            Nothing # t
    in Just arr'''' # t
  where
    fillToShift :  (i : Int)
                -> (shift : Int)
                -> (bs : ByteString)
                -> (arr : MArray s (length bs) Int)
                -> F1 s (Maybe (MArray s (length bs) Int))
    fillToShift i shift bs arr t =
      let False   := i == shift
            | True =>
                Just arr # t
          Just i' := tryNatToFin (cast {to=Nat} i)
            | Nothing =>
                Nothing # t
          ()  # t := set arr i' shift t
        in assert_total (fillToShift (i + 1) shift bs arr t)
    prefixShift :  (idx : Int)
                -> (j : Int)
                -> (bs : ByteString)
                -> (suff : MArray s (length bs) Int)
                -> (arr : MArray s (length bs) Int)
                -> F1 s (Maybe (MArray s (length bs) Int))
    prefixShift idx j bs suff arr t =
      let False      := idx < 0
            | True =>
                Just arr # t
          Just idx'  := tryNatToFin (cast {to=Nat} idx)
            | Nothing =>
                Nothing # t
          idx''  # t := get suff idx' t
          True       := idx'' ==  (idx + 1)
            | False =>
                assert_total (prefixShift (idx - 1) j bs suff arr t)
          shift      := (cast {to=Int} (minus (length bs) 1)) - idx
          arr'   # t := fillToShift j shift bs arr t
          Just arr'' := arr'
            | Nothing =>
                Nothing # t
        in assert_total (prefixShift (idx - 1) shift bs suff arr'' t)                                      
    suffixShift :  (idx : Int)
                -> (bs : ByteString)
                -> (suff : MArray s (length bs) Int)
                -> (arr : MArray s (length bs) Int)
                -> F1 s (Maybe (MArray s (length bs) Int))
    suffixShift idx bs suff arr t =
      let patend       := cast {to=Int} (minus (length bs) 1)
          False        := idx >= patend
            | True =>
                Just arr # t
          Just idx'    := tryNatToFin (cast {to=Nat} idx)
            | Nothing =>
                Nothing # t
          idx''    # t := get suff idx' t
          target       := patend - idx''
          Just target' := tryNatToFin (cast {to=Nat} target)
            | Nothing =>
                Nothing # t
          value        := patend - idx
          ()       # t := set arr target' value t
        in assert_total (suffixShift (idx + 1) bs suff arr t)
