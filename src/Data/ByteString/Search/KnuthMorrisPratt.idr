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

||| Returns a list of starting positions of a pattern `ByteString`
||| (0-based) across the list of target `ByteString`s.
private
matcher :  Bool
        -> ByteString
        -> List ByteString
        -> F1 s (List Nat)
matcher overlap pat chunks t =
  let bords     # t := kmpBorders pat t
      searcher' # t := searcher Z Z pat chunks Lin bords overlap t
    in (searcher' <>> []) # t
  where
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

||| Splits a ByteString at the first match of pat in target.
|||
||| This function uses the Knuth-Morris-Pratt matcher (with overlap = False) to
||| locate the earliest occurrence of pat in target.  If the pattern is
||| found at index i, the pattern ByteString pat is split at that index,
||| returning the prefix and suffix as a pair (before, after).
|||
||| If the pattern does not occur in the target, (pat, empty) is returned.
||| In other words, the entire pattern becomes the “before” part and the
||| “after” part is an empty ByteString.
|||
export
breakKMP :  (pat : ByteString)
         -> (target : ByteString)
         -> {0 prfpat : So (not $ null pat)}
         -> {0 prftarget : So (not $ null target)}
         -> {0 prflength : So ((length target) >= (length pat))}
         -> F1 s (ByteString, ByteString)
breakKMP pat target {prfpat} {prftarget} {prflength} t =
   let matcher' # t := matcher False pat [target] t
     in case matcher' of
          []       =>
            (target, empty) # t
          (i :: _) =>
            let target' := splitAt (cast {to=Nat} i) target
              in case target' of
                   Nothing       =>
                     (assert_total $ idris_crash "Data.ByteString.Search.KnuthMorrisPratt.breakKMP: can't split ByteString") # t
                   Just target'' =>
                     target'' # t

||| Splits a ByteString after the first match of pat in target.
|||
||| This function uses the Knuth-Morris-Pratt matcher (with overlap = False) to
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
breakAfterKMP : (pat : ByteString)
              -> (target : ByteString)
              -> {0 prfpat : So (not $ null pat)}
              -> {0 prftarget : So (not $ null target)}
              -> {0 prflength : So ((length target) >= (length pat))}
              -> F1 s (ByteString, ByteString)
breakAfterKMP pat target {prfpat} {prftarget} {prflength} t =
   let matcher' # t := matcher False pat [target] t
     in case matcher' of
          []       =>
            (target, empty) # t
          (i :: _) =>
            let target' := splitAt (plus (cast {to=Nat} i) (length pat)) target
              in case target' of
                   Nothing    =>
                     (assert_total $ idris_crash "Data.ByteString.Search.KnuthMorrisPratt.breakAfterKMP: can't split ByteString") # t
                   Just target'' =>
                     target'' # t

||| Splits a ByteString into a list of pieces according to repeated
||| matches of target, keeping the matching prefix of pat
||| at the front of each produced chunk.
|||
||| This function repeatedly searches target for occurrences of pat
||| (using the Knuth-Morris-Pratt matcher with overlap = False).  Each time a
||| match is found at index i, the prefix of pat up to i + length pat
||| is emitted as the next chunk, and the function continues processing the
||| remaining suffix of pat.
|||
||| Unlike breakKMP or breakAfterKMP, this function performs repeated
||| splitting until the entire pattern has been consumed, producing a
||| list of ByteStrings.
|||
export
splitKeepFrontKMP :  (pat : ByteString)
                  -> (target : ByteString)
                  -> {0 prfpat : So (not $ null pat)}
                  -> {0 prftarget : So (not $ null target)}
                  -> {0 prflength : So ((length target) >= (length pat))}
                  -> F1 s (List ByteString)
splitKeepFrontKMP pat target {prfpat} {prftarget} {prflength} t =
  let splitter' # t := splitter pat target Lin t
    in (splitter' <>> []) # t
  where
    psSplitter :  (pat : ByteString)
               -> (target : ByteString)
               -> (final : SnocList ByteString)
               -> F1 s (SnocList ByteString)
    psSplitter pat target final t =
      let matcher' # t := matcher False pat [(drop (length pat) target)] t
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
      let matcher' # t := matcher False pat [target] t
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
||| matches of pat inside target, keeping the matching
||| suffix of pat at the end of each produced chunk.
|||
||| This function repeatedly searches target for occurrences of pat
||| (using the Knuth-Morris-Pratt matcher with overlap = False).  Each time a
||| match is found at index i, the next chunk emitted is the prefix of
||| target of length i + length pat, which includes the entire matched
||| occurrence of pat at its end.
|||
||| After emitting this chunk, the function continues splitting the
||| remainder of target until all input has been consumed.
|||
||| Unlike splitKeepFrontKMP, which keeps the matched prefix of pat
||| at the front of each chunk, splitKeepEndKMP ensures the match
||| appears at the end of each chunk.
|||
||| If pat does not occur in target, the result is a singleton list
||| containing the original target.
|||
export
splitKeepEndKMP :  (pat : ByteString)
                -> (target : ByteString)
                -> {0 prfpat : So (not $ null pat)}
                -> {0 prftarget : So (not $ null target)}
                -> {0 prflength : So ((length target) >= (length pat))}
                -> F1 s (List ByteString)
splitKeepEndKMP pat target {prfpat} {prftarget} {prflength} t =
  let splitter' # t := splitter pat target Lin t
    in (splitter' <>> []) # t
  where
    splitter :  (pat : ByteString)
             -> (target : ByteString)
             -> (final : SnocList ByteString)
             -> F1 s (SnocList ByteString)
    splitter pat target final t =
      let matcher' # t := matcher False pat [target] t
        in case matcher' of
             []       =>
               let final' := final :< target
                 in final' # t
             (i :: _) =>
               let length' := plus (cast {to=Nat} i) (length pat)
                   final'  := final :< (take length' target)
                 in assert_total (splitter pat (drop length' target) final' t)

||| Splits a ByteString into a list of pieces according to repeated
||| matches of pat inside target, dropping each matched
||| occurrence from the output entirely.
|||
||| This function repeatedly searches target for occurrences of pat
||| (using the Knuth-Morris-Pratt matcher with overlap = False).  Each time a
||| match is found at index i, the prefix of target of length i
||| (that is, the portion preceding the match) is emitted as the next
||| chunk.  The matched substring itself is not included.
|||
||| After emitting this prefix, the function continues splitting the
||| remainder of target, skipping over the full match of length
||| i + length pat.  This process continues until the entire target
||| has been consumed.
|||
||| Unlike splitKeepFrontKMP and splitKeepEndKMP, which include the
||| matched pattern in each emitted chunk, splitDropKMP removes all
||| occurrences of pat from the output.
|||
||| If pat does not occur in target, the result is a singleton list
||| containing the original target.
|||
export
splitDropKMP :  (pat : ByteString)
             -> (target : ByteString)
             -> {0 prfpat : So (not $ null pat)}
             -> {0 prftarget : So (not $ null target)}
             -> {0 prflength : So ((length target) >= (length pat))}
             -> F1 s (List ByteString)
splitDropKMP pat target {prfpat} {prftarget} {prflength} t =
  let splitter' # t := splitter pat target Lin t
    in (splitter' <>> []) # t
  where
    splitter :  (pat : ByteString)
             -> (target : ByteString)
             -> (final : SnocList ByteString)
             -> F1 s (SnocList ByteString)
    splitter pat target final t =
      let matcher' # t := matcher False pat [target] t
        in case matcher' of
             []       =>
               let final' := final :< target
                 in final' # t
             (i :: _) =>
               let length' := plus (cast {to=Nat} i) (length pat)
                   final'  := final :< (take (cast {to=Nat} i) target)
                 in assert_total (splitter pat (drop length' target) final' t)
