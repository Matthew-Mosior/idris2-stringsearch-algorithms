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
        let patend := minus (length pat) (S 0)
            strend := minus (length target) (S 0)
          in case (cast {to=Int} strend) < stri of
               True  =>
                 final # t
               False =>       
                 let target' := index (cast {to=Nat} stri) target
                   in case target' of
                        Nothing       =>
                          (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.checkEnd: can't index into ByteString") # t
                        Just target'' =>
                          let pat'   := index patend pat
                            in case pat' of
                                 Nothing    =>
                                   (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.checkEnd: can't index into ByteString") # t
                                 Just pat'' =>
                                   case target'' == pat'' of
                                     True  =>
                                       assert_total (findMatch (stri - (cast {to=Int} patend)) (cast {to=Int} (minus patend (S 0))) pat target final occurrencesarr suffixshiftarr overlap t)
                                     False =>
                                       case tryNatToFin (cast {to=Nat} target'') of
                                         Nothing        =>
                                           (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.checkEnd: can't convert Nat to Fin") # t
                                         Just target''' =>
                                           let target'''' # t := get occurrencesarr target''' t
                                               newtarget      := stri + ((cast {to=Int} patend) + target'''')
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
                                                            assert_total (checkEnd (diff' + (cast {to=Int} (minus (length pat) (S 0)))) pat target final' occurrencesarr suffixshiftarr overlap t)
                                                          False =>
                                                            assert_total (afterMatch diff' (cast {to=Int} (minus (length pat) (S 0))) pat target final' occurrencesarr suffixshiftarr overlap t)
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
                                                        assert_total (checkEnd (diff' + (cast {to=Int} (minus (length pat) (S 0)))) pat target final' occurrencesarr suffixshiftarr overlap t)
                                                      False =>
                                                        assert_total (afterMatch diff' (cast {to=Int} (minus (length pat) (S 0))) pat target final' occurrencesarr suffixshiftarr overlap t)
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
                                          diff'     := diff + (max (pati + occur) (cast {to=Int} suff))
                                          maxdiff   := minus (length target) (length pat)
                                        in case (cast {to=Int} maxdiff) < diff' of
                                             True  =>
                                               let final' := final :< diff
                                                 in final' # t
                                             False =>
                                               assert_total (checkEnd (diff' + (cast {to=Int} (minus (length pat) (S 0)))) pat target final occurrencesarr suffixshiftarr overlap t)
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
                                                        assert_total (afterMatch diff' (cast {to=Int} (minus (length pat) (S 0))) pat target final' occurrencesarr suffixshiftarr overlap t)
                                             False =>
                                               assert_total (afterMatch diff (pati - 1)  pat target final occurrencesarr suffixshiftarr overlap t)
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
                                                    assert_total (afterMatch diff' (cast {to=Int} (minus (length pat) (S 0))) pat target final' occurrencesarr suffixshiftarr overlap t)
                                         False =>
                                           assert_total (afterMatch diff (pati - 1) pat target final occurrencesarr suffixshiftarr overlap t)
                            False =>
                              case pati == (cast {to=Int} (minus (length pat) (S 0))) of
                                True  =>
                                  case tryNatToFin (cast {to=Nat} diffpati') of
                                    Nothing         =>
                                      (assert_total $ idris_crash "Data.ByteString.Search.BoyerMoore.matcher.afterMatch: can't convert Nat to Fin") # t
                                    Just diffpati'' =>
                                      let occur # t := get occurrencesarr diffpati'' t
                                          occur'    := diff + (2 * (cast {to=Int} (minus (length pat) (S 0)))) + occur
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
                                          let final'        := final :< diff
                                              occur     # t := get occurrencesarr diffpati'' t
                                              goodshift # t := get suffixshiftarr pati'' t
                                              badshift      := pati + occur
                                              diff'         := diff + (max badshift goodshift)
                                              maxdiff       := minus (length target) (length pat)
                                            in case (cast {to=Int} maxdiff) < diff' of
                                                 True  =>
                                                   final' # t
                                                 False =>
                                                   assert_total (checkEnd (diff + (cast {to=Int} (minus (length pat) (S 0)))) pat target final occurrencesarr suffixshiftarr overlap t)
                        
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
||| matchBM "AN" "ANPANMAN" => [0, 3, 6]
|||
export
matchBM :  (pat : ByteString)
        -> (target : ByteString)
        -> {0 prfpat : So (not $ null pat)}
        -> {0 prftarget : So (not $ null target)}
        -> F1 s (List Int)
matchBM pat target {prfpat} {prftarget} t =
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
||| | Start | Substring       | Match? | Explanation                                                      |
||| | ----- | --------------- | ------ | ---------------------------------------------------------------- |
||| | 0     | **"ABCABC"**ABC | Yes    | Full pattern matches starting at index 0.                        |
||| | 1     | A**"BCABCA"**BC | No     | Mismatch starts immediately after first letter.                  |
||| | 2     | AB**"CABCAA"**C | No     | Shift by suffix table → mismatch on 2nd char.                    |
||| | 3     | ABC**"ABC"**    | Yes    | Overlapping match starting at index 3 (because `"ABC"` repeats). |
||| 
||| indicesBM "ABCABC" "ABCABCABC" => [0, 3]
|||
export
indicesBM :  (pat : ByteString)
          -> (target : ByteString)
          -> {0 prfpat : So (not $ null pat)}
          -> {0 prftarget : So (not $ null target)}
          -> F1 s (List Int)
indicesBM pat target {prfpat} {prftarget} t =
  matcher True pat target t
