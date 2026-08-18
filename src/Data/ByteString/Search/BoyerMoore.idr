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
|||
private
matcher :  Bool
        -> ByteString
        -> ByteString
        -> F1 s (Maybe (List Int))
matcher overlap pat target t =
  let False                 := length pat == S Z
        | True =>
            let patzero        := index Z pat
                Just patzero'  := patzero
                  | Nothing =>
                      Nothing # t
                headelem       := elemIndex patzero' pat
                Just headelem' := headelem
                  | Nothing =>
                      Nothing # t
              in Just ((cast {to=Int} headelem') :: []) # t
      Yes patprf            := decSo (not $ null pat)
        | No _ =>
            Nothing # t
      occurrencesarr    # t := occurrences pat {prf=patprf} t
      Just occurrencesarr'  := occurrencesarr
        | Nothing =>
            Nothing # t
      suffixshiftsarr   # t := suffixShifts pat {prf=patprf} t
      Just suffixshiftsarr' := suffixshiftsarr
        | Nothing =>
            Nothing # t
      matches           # t := checkEnd (cast {to=Int} (minus (length pat) (S 0))) pat target Lin occurrencesarr' suffixshiftsarr' overlap t
      Just matches'         := matches
        | Nothing =>
            Nothing # t
    in Just (matches' <>> []) # t
  where
    mutual
      checkEnd :  (stri : Int)
               -> (pat : ByteString)
               -> (target : ByteString)
               -> (final : SnocList Int)
               -> (occurrencesarr : MArray s 256 Int)
               -> (suffixshiftsarr : MArray s (length pat) Int)
               -> (overlap : Bool)
               -> F1 s (Maybe (SnocList Int))
      checkEnd stri pat target final occurrencesarr suffixshiftarr overlap t =
        let patend         := (cast {to=Int} (length pat)) - 1
            strend         := (cast {to=Int} (length target)) - 1
            False          := strend < stri
              | True =>
                  Just final # t
            target'        := index (cast {to=Nat} stri) target
            Just target''  := target'
              | Nothing =>
                  Nothing # t
            pat'           := index (cast {to=Nat} patend) pat
            Just pat''     := pat'
              | Nothing =>
                  Nothing # t
            False          := target'' == pat''
              | True =>
                  assert_total (findMatch (stri - patend) (patend - 1) pat target final occurrencesarr suffixshiftarr overlap t)
            Just target''' := tryNatToFin (cast {to=Nat} target'')
              | Nothing =>
                  Nothing # t
            target'''' # t := get occurrencesarr target''' t
            newtarget      := stri + patend + target''''
          in assert_total (checkEnd newtarget pat target final occurrencesarr suffixshiftarr overlap t)
      findMatch :  (diff : Int)
                -> (pati : Int)
                -> (pat : ByteString)
                -> (target : ByteString)
                -> (final : SnocList Int)
                -> (occurrencesarr : MArray s 256 Int)
                -> (suffixshiftsarr : MArray s (length pat) Int)
                -> (overlap : Bool)
                -> F1 s (Maybe (SnocList Int))
      findMatch diff pati pat target final occurrencesarr suffixshiftarr overlap t =
        let diffpati       := index (cast {to=Nat} (diff + pati)) target
            Just diffpati' := diffpati
              | Nothing =>
                  Nothing # t
            pati'          := index (cast {to=Nat} pati) pat
            Just pati''    := pati'
              | Nothing =>
                  Nothing # t
            True           := diffpati' == pati''
              | False =>
                  let Just diffpati'' := tryNatToFin (cast {to=Nat} diffpati')
                        | Nothing =>
                            Nothing # t
                      Just pati'''    := tryNatToFin (cast {to=Nat} pati)
                        | Nothing =>
                            Nothing # t
                      occur       # t := get occurrencesarr diffpati'' t
                      suff        # t := get suffixshiftarr pati''' t
                      diff'           := diff + (max (pati + occur) suff)
                      maxdiff         := minus (length target) (length pat)
                      False           := (cast {to=Int} maxdiff) < diff'
                        | True =>
                            Just final # t
                    in assert_total (checkEnd (diff' + ((cast {to=Int} (length pat)) - 1)) pat target final occurrencesarr suffixshiftarr overlap t)
            True           := pati == 0
              | False =>
                  assert_total (findMatch diff (pati - 1) pat target final occurrencesarr suffixshiftarr overlap t)
            final'         := final :< diff
            True           := overlap
              | False =>
                  let skip    := length pat
                      diff'   := diff + (cast {to=Int} skip)
                      maxdiff := minus (length target) (length pat)
                      False   := (cast {to=Int} maxdiff) < diff'
                        | True =>
                            Just final' # t
                      False   := skip == (length pat)
                        | True =>
                            assert_total (checkEnd (diff' + ((cast {to=Int} (length pat)) - 1)) pat target final' occurrencesarr suffixshiftarr overlap t)
                    in assert_total (afterMatch diff' ((cast {to=Int} (length pat)) - 1) pat target final' occurrencesarr suffixshiftarr overlap t)
            Just zero      := tryNatToFin Z
              | Nothing =>
                  Nothing # t
            skip       # t := get suffixshiftarr zero t
            diff'          := diff + skip
            maxdiff        := minus (length target) (length pat)
            False          := (cast {to=Int} maxdiff) < diff'
              | True =>
                  Just final' # t
            False          := skip == (cast {to=Int} (length pat))
              | True =>
                  assert_total (checkEnd (diff' + ((cast {to=Int} (length pat)) - 1)) pat target final' occurrencesarr suffixshiftarr overlap t)
          in assert_total (afterMatch diff' ((cast {to=Int} (length pat)) - 1) pat target final' occurrencesarr suffixshiftarr overlap t)
      afterMatch :  (diff : Int)
                 -> (pati : Int)
                 -> (pat : ByteString)
                 -> (target : ByteString)
                 -> (final : SnocList Int)
                 -> (occurrencesarr : MArray s 256 Int)
                 -> (suffixshiftsarr : MArray s (length pat) Int)
                 -> (overlap : Bool)
                 -> F1 s (Maybe (SnocList Int))
      afterMatch diff pati pat target final occurrencesarr suffixshiftarr overlap t =
        let diffpati       := index (cast {to=Nat} (diff + pati)) target
            Just diffpati' := diffpati
              | Nothing =>
                  Nothing # t
            pati'          := index (cast {to=Nat} pati) pat
            Just pati''    := pati'
              | Nothing =>
                  Nothing # t
            True           := diffpati' == pati''
              | False =>
                  let False           := pati == ((cast {to=Int} (length pat)) - 1)
                        | True =>
                            let Just diffpati'' := tryNatToFin (cast {to=Nat} diffpati')
                                  | Nothing =>
                                      Nothing # t
                                occur       # t := get occurrencesarr diffpati'' t
                                occur'          := diff + (2 * ((cast {to=Int} (length pat)) - 1)) + occur
                              in assert_total (checkEnd occur' pat target final occurrencesarr suffixshiftarr overlap t)
                      Just diffpati'' := tryNatToFin (cast {to=Nat} diffpati')
                        | Nothing =>
                            Nothing # t
                      Just pati'''    := tryNatToFin (cast {to=Nat} pati)
                        | Nothing =>
                            Nothing # t
                      occur       # t := get occurrencesarr diffpati'' t
                      goodshift   # t := get suffixshiftarr pati''' t
                      badshift        := pati + occur
                      diff'           := diff + (max badshift goodshift)
                      maxdiff         := minus (length target) (length pat)
                      False           := (cast {to=Int} maxdiff) < diff'
                        | True =>
                            Just final # t
                    in assert_total (checkEnd (diff + ((cast {to=Int} (length pat)) - 1)) pat target final occurrencesarr suffixshiftarr overlap t)
            True           := overlap
              | False =>
                  let kept := minus (length pat) (length pat)
                      True := pati == (cast {to=Int} kept)
                        | False =>
                            assert_total (afterMatch diff (pati - 1) pat target final occurrencesarr suffixshiftarr overlap t)
                      final'  := final :< diff
                      skip    := length pat
                      diff'   := diff + (cast {to=Int} skip)
                      maxdiff := minus (length target) (length pat)
                      False   := (cast {to=Int} maxdiff) < diff'
                        | True =>
                            Just final' # t
                    in assert_total (afterMatch diff' ((cast {to=Int} (length pat)) - 1) pat target final' occurrencesarr suffixshiftarr overlap t)
            Just zero      := tryNatToFin Z
              | Nothing =>
                  Nothing # t
            skip       # t := get suffixshiftarr zero t
            kept           := (cast {to=Int} (length pat)) - skip
            True           := pati == kept
              | False =>
                  assert_total (afterMatch diff (pati - 1) pat target final occurrencesarr suffixshiftarr overlap t)
            final'         := final :< diff
            diff'          := diff + skip
            maxdiff        := minus (length target) (length pat)
            False          := (cast {to=Int} maxdiff) < diff'
              | True =>
                  Just final' # t
          in assert_total (afterMatch diff' ((cast {to=Int} (length pat)) - 1) pat target final' occurrencesarr suffixshiftarr overlap t)
                        
||| Performs a string search on a `ByteString` utilizing a Boyer-Moore algorithm.
|||
||| This function finds all (0-based) starting indices of the non-empty pattern `ByteString`
||| pat within the non-empty target `ByteString`.
|||
||| Example:
|||
||| | pat  | target     |
||| | ---- | ---------- |
||| | "AN" | "ANPANMAN" |
|||
||| | s | window T[s..s+1] | comparisons (right→left)      | result    |                  bad-char |     good-suffix | chosen shift | next s |
||| | - | ---------------- | ----------------------------- | --------- | ------------------------- | --------------- | ------------ | ------ |
||| | 0 | **AN**           | j=1: N==N ✓ → j=0: A==A ✓     | **MATCH** |                         — | (after match) 2 |            2 |      2 |
||| | 1 | N**P**           | j=1: N vs P → mismatch at j=1 | mismatch  | lastOcc('P')=-1 → bad = 2 | suffShifts[1]=1 |        **2** |      3 |
||| | 2 | P**A**           | j=1: N vs A → mismatch at j=1 | mismatch  |  lastOcc('A')=0 → bad = 1 |        good = 1 |        **1** |      3 |
||| | 3 | **AN**           | j=1: N==N ✓ → j=0: A==A ✓     | **MATCH** |                         — | (after match) 2 |            2 |      5 |
||| | 4 | N**M**           | j=1: N vs M → mismatch at j=1 | mismatch  | lastOcc('M')=-1 → bad = 2 |        good = 1 |        **2** |      6 |
||| | 5 | M**A**           | j=1: N vs A → mismatch at j=1 | mismatch  |  lastOcc('A')=0 → bad = 1 |        good = 1 |        **1** |      6 |
||| | 6 | **AN**           | j=1: N==N ✓ → j=0: A==A ✓     | **MATCH** |                         — | (after match) 2 |            2 |      — |
|||
||| matchBM "AN" "ANPANMAN" => Just [0, 3, 6]
|||
export
matchBM :  (pat : ByteString)
        -> (target : ByteString)
        -> {0 prfpat : So (not $ null pat)}
        -> {0 prftarget : So (not $ null target)}
        -> {0 prflength : So ((length target) >= (length pat))}
        -> F1 s (Maybe (List Int))
matchBM pat target {prfpat} {prftarget} {prflength} t =
  let matcher' # t   := matcher False pat target t
      Just matcher'' := matcher'
        | Nothing =>
            Nothing # t
    in Just matcher'' # t

||| Performs a string search on a `ByteString` utilizing a Boyer-Moore algorithm.
|||
||| This function finds all (0-based) indices (possibly overlapping)
||| of the non-empty pattern `ByteString` pat
||| within the non-empty target `ByteString`.
|||
||| Example:
|||
||| | pat   | target      |
||| | ----- | ----------- |
||| | "ABC" | "ABCABCABC" |
|||
||| | Align s   | Window       | Comparison Result                  | Chosen Shift                         | Next s   |
||| | --------- | ------------ | ---------------------------------- | ------------------------------------ | -------- |
||| |     0     | **ABCABC**   | MATCH                              | good-suffix after full match = 3     |     3    |
||| |     1     | A**BCABCA**  | MISMATCH on last char (`C` vs `A`) | max(bad=2, good=1) = 2               |     3    |
||| |     2     | AB**CABCAA** | MISMATCH on last char (`C` vs `B`) | max(bad=1, good=1) = 1               |     3    |
||| |     3     | ABC**ABC**   | MATCH                              | (would shift 3 again)                |     —    |
||| 
||| indicesBM "ABCABC" "ABCABCABC" => Just [0, 3]
|||
export
indicesBM :  (pat : ByteString)
          -> (target : ByteString)
          -> {0 prfpat : So (not $ null pat)}
          -> {0 prftarget : So (not $ null target)}
          -> {0 prflength : So ((length target) >= (length pat))}
          -> F1 s (Maybe (List Int))
indicesBM pat target {prfpat} {prftarget} {prflength} t =
  let matcher'   # t := matcher True pat target t
      Just matcher'' := matcher'
        | Nothing =>
            Nothing # t
    in Just matcher'' # t

||| Splits a ByteString at the first match of pat in target.
|||
||| This function uses the Boyer–Moore matcher (with overlap = False) to
||| locate the earliest occurrence of pat in target.  If the pattern is
||| found at index i, the pattern ByteString pat is split at that index,
||| returning the prefix and suffix as a pair (before, after).
|||
||| If the pattern does not occur in the target, (pat, empty) is returned.
||| In other words, the entire pattern becomes the “before” part and the
||| “after” part is an empty ByteString.
|||
export
breakBM :  (pat : ByteString)
        -> (target : ByteString)
        -> {0 prfpat : So (not $ null pat)}
        -> {0 prftarget : So (not $ null target)}
        -> {0 prflength : So ((length target) >= (length pat))}
        -> F1 s (Maybe (ByteString, ByteString))
breakBM pat target {prfpat} {prftarget} {prflength} t =
   let matcher'   # t := matcher False pat target t
       Just matcher'' := matcher'
         | Nothing =>
             Nothing # t
       (i :: _)       := matcher''
         | [] =>
             Just (target, empty) # t
       target'        := splitAt (cast {to=Nat} i) target
       Just target''  := target'
         | Nothing =>
             Nothing # t
     in Just target'' # t

||| Splits a ByteString after the first match of pat in target.
|||
||| This function uses the Boyer–Moore matcher (with overlap = False) to
||| find the earliest occurrence of pat in target.  If the pattern is
||| found at index i, this function splits pat at position i + length pat,
||| producing a pair (before, after) that places the entire matched region
||| into the prefix.
|||
||| If the pattern does not occur in target, the function returns
||| (pat, empty), the entire pattern is the “before” substring, and the
||| suffix is empty.
|||
export
breakAfterBM :  (pat : ByteString)
             -> (target : ByteString)
             -> {0 prfpat : So (not $ null pat)}
             -> {0 prftarget : So (not $ null target)}
             -> {0 prflength : So ((length target) >= (length pat))}
             -> F1 s (Maybe (ByteString, ByteString))
breakAfterBM pat target {prfpat} {prftarget} {prflength} t =
   let matcher'   # t := matcher False pat target t
       Just matcher'' := matcher'
         | Nothing =>
             Nothing # t
       (i :: _)       := matcher''
         | [] =>
             Just (target, empty) # t
       target'        := splitAt (plus (cast {to=Nat} i) (length pat)) target
       Just target''  := target'
         | Nothing =>
             Nothing # t
     in Just target'' # t

||| Splits a ByteString into a list of pieces according to repeated
||| matches of target, keeping the matching prefix of pat
||| at the front of each produced chunk.
|||
||| This function repeatedly searches target for occurrences of pat
||| (using the Boyer–Moore matcher with overlap = False).  Each time a
||| match is found at index i, the prefix of pat up to i + length pat
||| is emitted as the next chunk, and the function continues processing the
||| remaining suffix of pat.
|||
||| Unlike breakBM or breakAfterBM, this function performs repeated
||| splitting until the entire pattern has been consumed, producing a
||| list of ByteStrings.
|||
export
splitKeepFrontBM :  (pat : ByteString)
                 -> (target : ByteString)
                 -> {0 prfpat : So (not $ null pat)}
                 -> {0 prftarget : So (not $ null target)}
                 -> {0 prflength : So ((length target) >= (length pat))}
                 -> F1 s (Maybe (List ByteString))
splitKeepFrontBM pat target {prfpat} {prftarget} {prflength} t =
  let splitter'   # t := splitter pat target Lin t
      Just splitter'' := splitter'
        | Nothing =>
            Nothing # t
    in Just (splitter'' <>> []) # t
  where
    psSplitter :  (pat : ByteString)
               -> (target : ByteString)
               -> (final : SnocList ByteString)
               -> F1 s (Maybe (SnocList ByteString))
    psSplitter pat target final t =
      let matcher'   # t := matcher False pat (drop (length pat) target) t
          Just matcher'' := matcher'
            | Nothing =>
                Nothing # t
          (i :: _)       := matcher''
            | [] =>
                let final' := final :< target
                  in Just final' # t
          length'        := plus (cast {to=Nat} i) (length pat)
          final'         := final :< (take length' target)
        in assert_total (psSplitter pat (drop length' target) final' t) 
    splitter :  (pat : ByteString)
             -> (target : ByteString)
             -> (final : SnocList ByteString)
             -> F1 s (Maybe (SnocList ByteString))
    splitter pat target final t =
      let matcher'   # t := matcher False pat target t
          Just matcher'' := matcher'
            | Nothing =>
                Nothing # t
          (i :: _)       := matcher''
            | [] =>
                let final' := final :< target
                  in Just final' # t
          False          := i == 0
            | True =>
                assert_total (psSplitter pat target final t)
          final'         := final :< (take (cast {to=Nat} i) target)
        in assert_total (psSplitter pat (drop (cast {to=Nat} i) target) final' t) 

||| Splits a ByteString into a list of pieces according to repeated
||| matches of pat inside target, keeping the matching
||| suffix of pat at the end of each produced chunk.
|||
||| This function repeatedly searches target for occurrences of pat
||| (using the Boyer–Moore matcher with overlap = False).  Each time a
||| match is found at index i, the next chunk emitted is the prefix of
||| target of length i + length pat, which includes the entire matched
||| occurrence of pat at its end.
|||
||| After emitting this chunk, the function continues splitting the
||| remainder of target until all input has been consumed.
|||
||| Unlike splitKeepFrontBM, which keeps the matched prefix of pat
||| at the front of each chunk, splitKeepEndBM ensures the match
||| appears at the end of each chunk.
|||
||| If pat does not occur in target, the result is a singleton list
||| containing the original target.
|||
export
splitKeepEndBM :  (pat : ByteString)
               -> (target : ByteString)
               -> {0 prfpat : So (not $ null pat)}
               -> {0 prftarget : So (not $ null target)}
               -> {0 prflength : So ((length target) >= (length pat))}
               -> F1 s (Maybe (List ByteString))
splitKeepEndBM pat target {prfpat} {prftarget} {prflength} t =
  let splitter'   # t := splitter pat target Lin t
      Just splitter'' := splitter'
        | Nothing =>
            Nothing # t
    in Just (splitter'' <>> []) # t
  where
    splitter :  (pat : ByteString)
             -> (target : ByteString)
             -> (final : SnocList ByteString)
             -> F1 s (Maybe (SnocList ByteString))
    splitter pat target final t =
      let matcher'   # t := matcher False pat target t
          Just matcher'' := matcher'
            | Nothing =>
                Nothing # t
          (i :: _)       := matcher''
            | [] =>
                let final' := final :< target
                  in Just final' # t
          length'        := plus (cast {to=Nat} i) (length pat)
          final'         := final :< (take length' target)
        in assert_total (splitter pat (drop length' target) final' t)

||| Splits a ByteString into a list of pieces according to repeated
||| matches of pat inside target, dropping each matched
||| occurrence from the output entirely.
|||
||| This function repeatedly searches target for occurrences of pat
||| (using the Boyer–Moore matcher with overlap = False).  Each time a
||| match is found at index i, the prefix of target of length i
||| (that is, the portion preceding the match) is emitted as the next
||| chunk.  The matched substring itself is not included.
|||
||| After emitting this prefix, the function continues splitting the
||| remainder of target, skipping over the full match of length
||| i + length pat.  This process continues until the entire target
||| has been consumed.
|||
||| Unlike splitKeepFrontBM and splitKeepEndBM, which include the
||| matched pattern in each emitted chunk, splitDropBM removes all
||| occurrences of pat from the output.
|||
||| If pat does not occur in target, the result is a singleton list
||| containing the original target.
|||
export
splitDropBM :  (pat : ByteString)
            -> (target : ByteString)
            -> {0 prfpat : So (not $ null pat)}
            -> {0 prftarget : So (not $ null target)}
            -> {0 prflength : So ((length target) >= (length pat))}
            -> F1 s (Maybe (List ByteString))
splitDropBM pat target {prfpat} {prftarget} {prflength} t =
  let splitter' # t   := splitter pat target Lin t
      Just splitter'' := splitter'
        | Nothing =>
            Nothing # t
    in Just (splitter'' <>> []) # t
  where
    splitter :  (pat : ByteString)
             -> (target : ByteString)
             -> (final : SnocList ByteString)
             -> F1 s (Maybe (SnocList ByteString))
    splitter pat target final t =
      let matcher'   # t := matcher False pat target t
          Just matcher'' := matcher'
            | Nothing =>
                Nothing # t
          (i :: _)       := matcher''
            | [] =>
                let final' := final :< target
                  in Just final' # t
          length'        := plus (cast {to=Nat} i) (length pat)
          final'         := final :< (take (cast {to=Nat} i) target)
        in assert_total (splitter pat (drop length' target) final' t)

||| Replaces all non-overlapping occurrences of a pattern in a ByteString
||| using the Boyer–Moore matcher.
|||
||| This function repeatedly searches target for occurrences of pat
||| (using matcher False). Each time a match is found at index i:
|||
||| * If i == 0, the match is at the current position. The matched
|||   segment is dropped and sub is appended to the result (unless
|||   sub is empty, in which case nothing is appended).
|||
||| * If i > 0, the prefix take i target is appended to the result,
|||   followed by sub (unless sub is empty). The matched segment is
|||   then dropped and processing continues on the remaining suffix.
|||
||| If no further matches are found, the remaining target is appended
||| unchanged and the result is returned.
|||
||| The result is accumulated via a `SnocList` and returned as a `List
||| ByteString`, preserving left-to-right order of the produced chunks.
|||
export
replaceBM :  (pat : ByteString)
          -> (sub : ByteString)
          -> (target : ByteString)
          -> {0 prfpat : So (not $ null pat)}
          -> {0 prftarget : So (not $ null target)}
          -> {0 prflength : So ((length target) >= (length pat))}
          -> F1 s (Maybe (List ByteString))
replaceBM pat sub target {prfpat} {prftarget} {prflength} t =
  let replacer'   # t := replacer pat sub target Lin t
      Just replacer'' := replacer'
        | Nothing =>
            Nothing # t
    in Just (replacer'' <>> []) # t
  where
    replacer :  (pat : ByteString)
             -> (sub : ByteString)
             -> (target : ByteString)
             -> (final : SnocList ByteString)
             -> F1 s (Maybe (SnocList ByteString))
    replacer pat sub target final t =
      let matcher'   # t := matcher False pat target t
          Just matcher'' := matcher'
            | Nothing =>
                Nothing # t
          (i :: _)       := matcher''
            | [] =>
                let final' := final :< target
                  in Just final' # t
          Z              := cast {to=Nat} i
            | _ =>
                let False := null sub
                      | True =>
                          let length' := plus (cast {to=Nat} i) (length pat) 
                              final'  := final :< (take (cast {to=Nat} i) target)
                            in assert_total (replacer pat sub (drop length' target) final' t)
                    length' := plus (cast {to=Nat} i) (length pat) 
                    final'  := final :< (take (cast {to=Nat} i) target) :< sub
                  in assert_total (replacer pat sub (drop length' target) final' t)
          False          := null sub
            | True =>
                assert_total (replacer pat sub (drop (length pat) target) final t)
          final'         := final :< sub
        in assert_total (replacer pat sub (drop (length pat) target) final') t
