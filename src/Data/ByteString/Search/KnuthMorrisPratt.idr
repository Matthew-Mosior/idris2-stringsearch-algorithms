||| Fast Knuth-Morris-Pratt search of ByteStrings
module Data.ByteString.Search.KnuthMorrisPratt

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
      let chunks' # t := go Z chunks Lin t
        in Z :: chunks' # t
    False =>
      let bords     # t := kmpBorders pat t
          searcher' # t := searcher Z Z pat chunks Lin bords overlap t
        in (searcher' <>> []) # t
  where
    go :  Nat
       -> List ByteString
       -> SnocList Nat
       -> F1 s (List Nat)
    go _     []      sl t =
      (sl <>> []) # t
    go prior (s::ss) sl t =
      let l      := length s
          prior' := plus prior l
          s'     := [ prior' | i <- [1..l] ]
          sl'    := sl <>< s'
        in go prior' ss sl' t
    mutual
      findMatch :  (prior : Nat)
                -> (pati : Nat)
                -> (stri : Nat)
                -> (pat : ByteString)
                -> (strs : List ByteString)
                -> (final : SnocList Nat)
                -> (bords : MArray s (S (length pat)) Nat)
                -> (overlap : Bool)
                -> F1 s (SnocList Nat)
      findMatch _     _    _    _   []               final _     _       t =
        final # t
      findMatch prior pati stri pat strs@(str::rest) final bords overlap t =
        let patlen := length pat
          in case pati == patlen of
               True  =>
                 case overlap of
                   True  =>
                     case tryNatToFin patlen of
                       Nothing      =>
                         (assert_total $ idris_crash "Data.ByteString.Search.KnuthMorrisPratt.matcher.findMatch: can't index into ByteString") # t
                       Just patlen' =>
                         let final'  := minus (plus prior stri) patlen
                             ami # t := get bords patlen' t
                           in case ami == Z of
                                True  =>
                                  let final'' := final :< final'
                                    in assert_total (checkHead prior stri pat strs final'' bords overlap t)
                                False =>
                                  let final'' := final :< final'
                                    in assert_total (findMatch prior ami stri pat strs final'' bords overlap t)
                   False =>
                     let final'  := minus (plus prior stri) patlen
                         final'' := final :< final'
                       in assert_total (checkHead prior stri pat strs final'' bords overlap t)
               False =>
                 let strlen := length str
                   in case stri == strlen of
                        True  =>
                          assert_total (searcher (plus prior strlen) pati pat rest final bords overlap t)
                        False =>
                          let pati' := index pati pat
                            in case pati' of
                                 Nothing     =>
                                   (assert_total $ idris_crash "Data.ByteString.Search.KnuthMorrisPratt.matcher.findMatch: can't index into ByteString") # t
                                 Just pati'' =>
                                   let stri' := index stri str
                                     in case stri' of
                                          Nothing     =>
                                            (assert_total $ idris_crash "Data.ByteString.Search.KnuthMorrisPratt.matcher.findMatch: can't index into ByteString") # t
                                          Just stri'' =>
                                            case stri'' == pati'' of
                                              True  =>
                                                assert_total (findMatch prior (S pati) (S stri) pat strs final bords overlap t)
                                              False =>
                                                case tryNatToFin pati of
                                                  Nothing      =>
                                                    (assert_total $ idris_crash "Data.ByteString.Search.KnuthMorrisPratt.matcher.findMatch: can't convert Nat to Fin") # t        
                                                  Just pati''' =>
                                                    let pati'''' # t := get bords pati''' t
                                                      in case pati'''' == Z of
                                                           True  =>
                                                             assert_total (checkHead prior (S stri) pat strs final bords overlap t)
                                                           False =>
                                                             assert_total (findMatch prior pati'''' stri pat strs final bords overlap t)
      checkHead :  (prior : Nat)
                -> (stri : Nat)
                -> (pat : ByteString)
                -> (strs : List ByteString)
                -> (final : SnocList Nat)
                -> (bords : MArray s (S (length pat)) Nat)
                -> (overlap : Bool)
                -> F1 s (SnocList Nat)
      checkHead _     _    _   []               final _     _       t =
        final # t
      checkHead prior stri pat strs@(str::rest) final bords overlap t =
        let strlen := length str
          in case stri == strlen of
               True  =>
                 assert_total (searcher (plus prior strlen) Z pat rest final bords overlap t)
               False =>
                 let stri' := index stri str
                   in case stri' of
                        Nothing     =>
                          (assert_total $ idris_crash "Data.ByteString.Search.KnuthMorrisPratt.matcher.checkHead: can't index into ByteString") # t
                        Just stri'' =>
                          let patzero := index Z pat
                            in case patzero of
                                 Nothing       =>
                                   (assert_total $ idris_crash "Data.ByteString.Search.KnuthMorrisPratt.matcher.checkHead: can't index into ByteString") # t
                                 Just patzero' =>
                                   case stri'' == patzero' of
                                     True  =>
                                       assert_total (findMatch prior (S Z) (S stri) pat strs final bords overlap t)
                                     False =>
                                       assert_total (checkHead prior (S stri) pat strs final bords overlap t)
      searcher :  (prior : Nat)
               -> (patpos : Nat)
               -> (pat : ByteString)
               -> (strs : List ByteString)
               -> (final : SnocList Nat)
               -> (bords : MArray s (S (length pat)) Nat)
               -> (overlap : Bool)
               -> F1 s (SnocList Nat)
      searcher _     _      _   []   final _     _       t =
        final # t
      searcher prior Z      pat strs final bords overlap t =
        assert_total (checkHead prior Z pat strs final bords overlap t)
      searcher prior patpos pat strs final bords overlap t =
        assert_total (findMatch prior patpos Z pat strs final bords overlap t)

||| Performs a Knuth–Morris–Pratt string search on a `ByteString`.
|||
||| This function finds all (0-based) starting indices of the non-empty pattern `ByteString`
||| pat within the non-empty target `ByteString`, using the KMP border table
||| computed by `kmpBorders`.
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
||| matchKMP "AN" "ANPANMAN" => [0, 3, 6]
|||
export
matchKMP :  (pat : ByteString)
         -> (target : ByteString)
         -> {0 prfpat : So (not $ null pat)}
         -> {0 prftarget : So (not $ null target)}
         -> F1 s (List Nat)
matchKMP pat target {prfpat} {prftarget} t =
  matcher False pat [target] t

||| Performs a Knuth–Morris–Pratt string search on a `ByteString`.
|||
||| This function finds all (0-based) indices (possibly overlapping)
||| of the non-empty pattern `ByteString` pat
||| within the non-empty target `ByteString`, using the KMP border table
||| computed by `kmpBorders`.
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
||| indicesKMP "ABCABC" "ABCABCABC" => [0, 3]
|||
export
indicesKMP :  (pat : ByteString)
           -> (target : ByteString)
           -> {0 prfpat : So (not $ null pat)}
           -> {0 prftarget : So (not $ null target)}
           -> F1 s (List Nat)
indicesKMP pat target {prfpat} {prftarget} t =
  matcher True pat [target] t
