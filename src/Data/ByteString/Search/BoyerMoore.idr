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
        -> F1 s (List Int)
matcher overlap pat target t =
  case length pat == S Z of
    True  =>
      let patzero := index Z pat
        in case patzero of
             Nothing       =>
               (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher: can't index into ByteString") # t
             Just patzero' =>
               let headelem := elemIndex patzero' pat
                 in case headelem of
                      Nothing        =>
                        (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher: byte does not appear in ByteString") # t
                      Just headelem' =>
                        ((cast {to=Int} headelem') :: []) # t
    False =>
      case decSo $ (not $ null pat) of
        No  _      =>
           (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher: pattern is null") # t
        Yes patprf =>
          let occurrencesarr  # t := occurrences pat {prf=patprf} t
              suffixshiftsarr # t := suffixShifts pat {prf=patprf} t
              matches         # t := checkEnd (cast {to=Int} (minus (length pat) (S 0))) pat target Lin occurrencesarr suffixshiftsarr overlap t
            in (matches <>> []) # t
  where
    mutual
      checkEnd :  (stri : Int)
               -> (pat : ByteString)
               -> (target : ByteString)
               -> (final : SnocList Int)
               -> (occurrencesarr : MArray s 256 Int)
               -> (suffixshiftsarr : MArray s (length pat) Int)
               -> (overlap : Bool)
               -> F1 s (SnocList Int)
      checkEnd stri pat target final occurrencesarr suffixshiftarr overlap t =
        let patend := (cast {to=Int} (length pat)) - 1
            strend := (cast {to=Int} (length target)) - 1
          in case strend < stri of
               True  =>
                 final # t
               False =>       
                 let target' := index (cast {to=Nat} stri) target
                   in case target' of
                        Nothing       =>
                          (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.checkEnd: can't index into ByteString") # t
                        Just target'' =>
                          let pat' := index (cast {to=Nat} patend) pat
                            in case pat' of
                                 Nothing    =>
                                   (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.checkEnd: can't index into ByteString") # t
                                 Just pat'' =>
                                   case target'' == pat'' of
                                     True  =>
                                       assert_total (findMatch (stri - patend) (patend - 1) pat target final occurrencesarr suffixshiftarr overlap t)
                                     False =>
                                       case tryNatToFin (cast {to=Nat} target'') of
                                         Nothing        =>
                                           (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.checkEnd: can't convert Nat to Fin") # t
                                         Just target''' =>
                                           let target'''' # t := get occurrencesarr target''' t
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
                -> F1 s (SnocList Int)
      findMatch diff pati pat target final occurrencesarr suffixshiftarr overlap t =
        let diffpati := index (cast {to=Nat} (diff + pati)) target
          in case diffpati of
               Nothing        =>
                 (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.findMatch: can't index into ByteString") # t
               Just diffpati' =>
                 let pati' := index (cast {to=Nat} pati) pat
                   in case pati' of
                        Nothing     =>
                          (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.findMatch: can't index into ByteString") # t
                        Just pati'' =>
                          case diffpati' == pati'' of
                            True  =>
                              case pati == 0 of
                                True  =>
                                  let final' := final :< diff
                                    in case overlap of
                                         True  =>
                                           case tryNatToFin Z of
                                             Nothing   =>
                                               (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.findMatch: can't convert Nat to Fin") # t
                                             Just zero =>
                                               let skip # t := get suffixshiftarr zero t
                                                   diff'    := diff + skip
                                                   maxdiff  := minus (length target) (length pat)
                                                 in case (cast {to=Int} maxdiff) < diff' of
                                                      True  =>
                                                        final' # t
                                                      False =>
                                                        case skip == (cast {to=Int} (length pat)) of
                                                          True  =>
                                                            assert_total (checkEnd (diff' + ((cast {to=Int} (length pat)) - 1)) pat target final' occurrencesarr suffixshiftarr overlap t)
                                                          False =>
                                                            assert_total (afterMatch diff' ((cast {to=Int} (length pat)) - 1) pat target final' occurrencesarr suffixshiftarr overlap t)
                                         False =>
                                           let skip    := length pat
                                               diff'   := diff + (cast {to=Int} skip)
                                               maxdiff := minus (length target) (length pat)
                                             in case (cast {to=Int} maxdiff) < diff' of
                                                  True  =>
                                                    final' # t
                                                  False =>
                                                    case skip == (length pat) of
                                                      True  =>
                                                        assert_total (checkEnd (diff' + ((cast {to=Int} (length pat)) - 1)) pat target final' occurrencesarr suffixshiftarr overlap t)
                                                      False =>
                                                        assert_total (afterMatch diff' ((cast {to=Int} (length pat)) - 1) pat target final' occurrencesarr suffixshiftarr overlap t)
                                False =>
                                  assert_total (findMatch diff (pati - 1) pat target final occurrencesarr suffixshiftarr overlap t)
                            False =>
                              case tryNatToFin (cast {to=Nat} diffpati') of
                                Nothing         =>
                                  (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.findMatch: can't convert Nat to Fin") # t
                                Just diffpati'' =>
                                  case tryNatToFin (cast {to=Nat} pati) of
                                    Nothing    =>
                                      (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.findMatch: can't convert Nat to Fin") # t
                                    Just pati' =>
                                      let occur # t := get occurrencesarr diffpati'' t
                                          suff  # t := get suffixshiftarr pati' t
                                          diff'     := diff + (max (pati + occur) suff)
                                          maxdiff   := minus (length target) (length pat)
                                        in case (cast {to=Int} maxdiff) < diff' of
                                             True  =>
                                               final # t
                                             False =>
                                               assert_total (checkEnd (diff' + ((cast {to=Int} (length pat)) - 1)) pat target final occurrencesarr suffixshiftarr overlap t)
      afterMatch :  (diff : Int)
                 -> (pati : Int)
                 -> (pat : ByteString)
                 -> (target : ByteString)
                 -> (final : SnocList Int)
                 -> (occurrencesarr : MArray s 256 Int)
                 -> (suffixshiftsarr : MArray s (length pat) Int)
                 -> (overlap : Bool)
                 -> F1 s (SnocList Int)
      afterMatch diff pati pat target final occurrencesarr suffixshiftarr overlap t =
        let diffpati := index (cast {to=Nat} (diff + pati)) target
          in case diffpati of
               Nothing        =>
                 (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.afterMatch: can't index into ByteString") # t
               Just diffpati' =>
                 let pati' := index (cast {to=Nat} pati) pat
                   in case pati' of
                        Nothing     =>
                          (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.afterMatch: can't index into ByteString") # t
                        Just pati'' =>                          
                          case diffpati' == pati'' of
                            True  =>
                              case overlap of
                                True  =>
                                  case tryNatToFin Z of
                                    Nothing   =>
                                      (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.afterMatch: can't convert Nat to Fin") # t
                                    Just zero =>
                                      let skip # t := get suffixshiftarr zero t
                                          kept     := (cast {to=Int} (length pat)) - skip
                                        in case pati == kept of
                                             True  =>
                                               let final'  := final :< diff
                                                   diff'   := diff + skip
                                                   maxdiff := minus (length target) (length pat)
                                                 in case (cast {to=Int} maxdiff) < diff' of
                                                      True  =>
                                                        final' # t
                                                      False =>
                                                        assert_total (afterMatch diff' ((cast {to=Int} (length pat)) - 1) pat target final' occurrencesarr suffixshiftarr overlap t)
                                             False =>
                                               assert_total (afterMatch diff (pati - 1) pat target final occurrencesarr suffixshiftarr overlap t)
                                False =>
                                  let kept := minus (length pat) (length pat)
                                    in case pati == (cast {to=Int} kept) of
                                         True  =>
                                           let final'  := final :< diff
                                               skip    := length pat
                                               diff'   := diff + (cast {to=Int} skip)
                                               maxdiff := minus (length target) (length pat)
                                             in case (cast {to=Int} maxdiff) < diff' of
                                                  True  =>
                                                    final' # t
                                                  False =>
                                                    assert_total (afterMatch diff' ((cast {to=Int} (length pat)) - 1) pat target final' occurrencesarr suffixshiftarr overlap t)
                                         False =>
                                           assert_total (afterMatch diff (pati - 1) pat target final occurrencesarr suffixshiftarr overlap t)
                            False =>
                              case pati == ((cast {to=Int} (length pat)) - 1) of
                                True  =>
                                  case tryNatToFin (cast {to=Nat} diffpati') of
                                    Nothing         =>
                                      (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.afterMatch: can't convert Nat to Fin") # t
                                    Just diffpati'' =>
                                      let occur # t := get occurrencesarr diffpati'' t
                                          occur'    := diff + (2 * ((cast {to=Int} (length pat)) - 1)) + occur
                                        in assert_total (checkEnd occur' pat target final occurrencesarr suffixshiftarr overlap t)
                                False =>
                                  case tryNatToFin (cast {to=Nat} diffpati') of
                                    Nothing         =>
                                      (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.afterMatch: can't convert Nat to Fin") # t
                                    Just diffpati'' =>
                                      case tryNatToFin (cast {to=Nat} pati) of
                                        Nothing     =>
                                          (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.afterMatch: can't convert Nat to Fin") # t
                                        Just pati'' =>
                                          let occur     # t := get occurrencesarr diffpati'' t
                                              goodshift # t := get suffixshiftarr pati'' t
                                              badshift      := pati + occur
                                              diff'         := diff + (max badshift goodshift)
                                              maxdiff       := minus (length target) (length pat)
                                            in case (cast {to=Int} maxdiff) < diff' of
                                                 True  =>
                                                   final # t
                                                 False =>
                                                   assert_total (checkEnd (diff + ((cast {to=Int} (length pat)) - 1)) pat target final occurrencesarr suffixshiftarr overlap t)
                        
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
||| matchBM "AN" "ANPANMAN" => [0, 3, 6]
|||
export
matchBM :  (pat : ByteString)
        -> (target : ByteString)
        -> {0 prfpat : So (not $ null pat)}
        -> {0 prftarget : So (not $ null target)}
        -> {0 prflength : So ((length target) >= (length pat))}
        -> F1 s (List Int)
matchBM pat target {prfpat} {prftarget} {prflength} t =
  matcher False pat target t

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
||| indicesBM "ABCABC" "ABCABCABC" => [0, 3]
|||
export
indicesBM :  (pat : ByteString)
          -> (target : ByteString)
          -> {0 prfpat : So (not $ null pat)}
          -> {0 prftarget : So (not $ null target)}
          -> {0 prflength : So ((length target) >= (length pat))}
          -> F1 s (List Int)
indicesBM pat target {prfpat} {prftarget} {prflength} t =
  matcher True pat target t

||| Splits a ByteString at the first Boyer–Moore match of pat in target.
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
        -> F1 s (ByteString, ByteString)
breakBM pat target {prfpat} {prftarget} {prflength} t =
   let matcher' # t := matcher False pat target t
     in case matcher' of
          []       =>
            (target, empty) # t
          (i :: _) =>
            let target' := splitAt (cast {to=Nat} i) target
              in case target' of
                   Nothing       =>
                     (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.breakBM: can't split ByteString") # t
                   Just target'' =>
                     target'' # t

||| Splits a ByteString after the first Boyer–Moore match of pat in target.
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
             -> F1 s (ByteString, ByteString)
breakAfterBM pat target {prfpat} {prftarget} {prflength} t =
   let matcher' # t := matcher False pat target t
     in case matcher' of
          []       =>
            (target, empty) # t
          (i :: _) =>
            let target' := splitAt (plus (cast {to=Nat} i) (length pat)) target
              in case target' of
                   Nothing    =>
                     (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.breakBM: can't split ByteString") # t
                   Just target'' =>
                     target'' # t

||| Splits a ByteString into a list of pieces according to repeated
||| Boyer–Moore matches of target, keeping the matching prefix of pat
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
                 -> F1 s (List ByteString)
splitKeepFrontBM pat target {prfpat} {prftarget} {prflength} t =
  let splitter' # t := splitter pat target Lin t
    in (splitter' <>> []) # t
  where
    psSplitter :  (pat : ByteString)
               -> (target : ByteString)
               -> (final : SnocList ByteString)
               -> F1 s (SnocList ByteString)
    psSplitter pat target final t =
      let matcher' # t := matcher False pat (drop (length pat) target) t
        in case matcher' of
             []       =>
               let final' := final :< target
                 in final' # t
             (i :: _) => 
               let length' := plus (cast {to=Nat} i) (length pat)
                   final'  := final :< (take length' target)
                 in assert_total (psSplitter pat (drop length' target) final' t) 
    splitter :  (pat : ByteString)
             -> (target : ByteString)
             -> (final : SnocList ByteString)
             -> F1 s (SnocList ByteString)
    splitter pat target final t =
      let matcher' # t := matcher False pat target t
        in case matcher' of
             []       =>
               let final' := final :< target
                 in final' # t
             (i :: _) => 
               case i == 0 of
                 True  =>
                   assert_total (psSplitter pat target final t)
                 False =>
                   let final' := final :< (take (cast {to=Nat} i) target)
                     in assert_total (psSplitter pat (drop (cast {to=Nat} i) target) final' t) 

||| Splits a ByteString into a list of pieces according to repeated
||| Boyer–Moore matches of pat inside target, keeping the matching
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
               -> F1 s (List ByteString)
splitKeepEndBM pat target {prfpat} {prftarget} {prflength} t =
  let splitter' # t := splitter pat target Lin t
    in (splitter' <>> []) # t
  where
    splitter :  (pat : ByteString)
             -> (target : ByteString)
             -> (final : SnocList ByteString)
             -> F1 s (SnocList ByteString)
    splitter pat target final t =
      let matcher' # t := matcher False pat target t
        in case matcher' of
             []       =>
               let final' := final :< target
                 in final' # t
             (i :: _) => 
               let length' := plus (cast {to=Nat} i) (length pat)
                   final'  := final :< (take length' target)
                 in assert_total (splitter pat (drop length' target) final' t)

||| Splits a ByteString into a list of pieces according to repeated
||| Boyer–Moore matches of pat inside target, dropping each matched
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
            -> F1 s (List ByteString)
splitDropBM pat target {prfpat} {prftarget} {prflength} t =
  let splitter' # t := splitter pat target Lin t
    in (splitter' <>> []) # t
  where
    splitter :  (pat : ByteString)
             -> (target : ByteString)
             -> (final : SnocList ByteString)
             -> F1 s (SnocList ByteString)
    splitter pat target final t =
      let matcher' # t := matcher False pat target t
        in case matcher' of
             []       =>
               let final' := final :< target
                 in final' # t
             (i :: _) =>
               let length' := plus (cast {to=Nat} i) (length pat)
                   final'  := final :< (take (cast {to=Nat} i) target)
                 in assert_total (splitter pat (drop length' target) final' t)
