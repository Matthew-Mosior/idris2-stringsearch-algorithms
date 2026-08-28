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
|||
private
matcher :  Bool
        -> ByteString
        -> List ByteString
        -> F1 s (Maybe (List Nat))
matcher overlap pat chunks t =
  let patlen := length pat
      Just patzero := index Z pat
        | Nothing =>
            Nothing # t
      bords # t := kmpBorders pat t
      Just bords' := bords
        | Nothing =>
            Nothing # t
      Just patlenfin := tryNatToFin patlen
        | Nothing =>
            Nothing # t
      fullbord # t := get bords' patlenfin t
      result # t := searcher Z Z chunks Lin patlen patzero fullbord bords' t
      Just result' := result
        | Nothing =>
            Nothing # t
    in Just (result' <>> []) # t
  where
    mutual
      searcher :  (prior : Nat)
               -> (patpos : Nat)
               -> (strs : List ByteString)
               -> (final : SnocList Nat)
               -> (patlen : Nat)
               -> (patzero : Bits8)
               -> (fullbord : Nat)
               -> (bords : MArray s (S (length pat)) Nat)
               -> F1 s (Maybe (SnocList Nat))
      searcher _     _      []            final _      _       _        _     t =
        Just final # t
      searcher prior patpos (str :: rest) final patlen patzero fullbord bords t =
        let strlen := length str
            False  := patpos == Z
              | True =>
                  assert_total (checkHead prior Z str strlen rest final patlen patzero fullbord bords t)
          in assert_total (findMatch prior patpos Z str strlen rest final patlen patzero fullbord bords t)
      checkHead :  (prior : Nat)
                -> (stri : Nat)
                -> (str : ByteString)
                -> (strlen : Nat)
                -> (rest : List ByteString)
                -> (final : SnocList Nat)
                -> (patlen : Nat)
                -> (patzero : Bits8)
                -> (fullbord : Nat)
                -> (bords : MArray s (S (length pat)) Nat)
                -> F1 s (Maybe (SnocList Nat))
      checkHead prior stri str strlen rest final patlen patzero fullbord bords t =
        let False := stri == strlen
              | True =>
                  assert_total (searcher (plus prior strlen) Z rest final patlen patzero fullbord bords t)
            Just strbyte := index stri str
              | Nothing =>
                  Nothing # t
            nxtstri := S stri
            False := strbyte == patzero
              | True =>
                  assert_total (findMatch prior (S Z) nxtstri str strlen rest final patlen patzero fullbord bords t)
          in assert_total (checkHead prior nxtstri str strlen rest final patlen patzero fullbord bords t)
      findMatch :  (prior : Nat)
                -> (pati : Nat)
                -> (stri : Nat)
                -> (str : ByteString)
                -> (strlen : Nat)
                -> (rest : List ByteString)
                -> (final : SnocList Nat)
                -> (patlen : Nat)
                -> (patzero : Bits8)
                -> (fullbord : Nat)
                -> (bords : MArray s (S (length pat)) Nat)
                -> F1 s (Maybe (SnocList Nat))
      findMatch prior pati stri str strlen rest final patlen patzero fullbord bords t =
        let False := pati == patlen
              | True =>
                  let matchidx := minus (plus prior stri) patlen
                      final'   := final :< matchidx
                      False    := overlap
                        | True =>
                            let False := fullbord == Z
                                  | True =>
                                      assert_total (checkHead prior stri str strlen rest final' patlen patzero fullbord bords t)
                              in assert_total (findMatch prior fullbord stri str strlen rest final' patlen patzero fullbord bords t)
                    in assert_total (checkHead prior stri str strlen rest final' patlen patzero fullbord bords t)
            False := stri == strlen
              | True =>
                  assert_total (searcher (plus prior strlen) pati rest final patlen patzero fullbord bords t)
            Just strbyte := index stri str
              | Nothing =>
                  Nothing # t
          in assert_total (compareAt prior pati stri strbyte str strlen rest final patlen patzero fullbord bords t)
      compareAt :  (prior : Nat)
                -> (pati : Nat)
                -> (stri : Nat)
                -> (strbyte : Bits8)
                -> (str : ByteString)
                -> (strlen : Nat)
                -> (rest : List ByteString)
                -> (final : SnocList Nat)
                -> (patlen : Nat)
                -> (patzero : Bits8)
                -> (fullbord : Nat)
                -> (bords : MArray s (S (length pat)) Nat)
                -> F1 s (Maybe (SnocList Nat))
      compareAt prior pati stri strbyte str strlen rest final patlen patzero fullbord bords t =
          let Just patbyte := index pati pat
                | Nothing =>
                    Nothing # t
              False := strbyte == patbyte
                | True =>
                    assert_total (findMatch prior (S pati) (S stri) str strlen rest final patlen patzero fullbord bords t)
              Just patfin := tryNatToFin pati
                | Nothing =>
                    Nothing # t
              fallback # t := get bords patfin t
              False := fallback == Z
                | True =>
                    assert_total (checkHead prior (S stri) str strlen rest final patlen patzero fullbord bords t)
            in assert_total (compareAt prior fallback stri strbyte str strlen rest final patlen patzero fullbord bords t)

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
||| matchKMP "AN" "ANPANMAN" => Just [0, 3, 6]
|||
export
matchKMP :  (pat : ByteString)
         -> (target : ByteString)
         -> {0 prfpat : So (not $ null pat)}
         -> {0 prftarget : So (not $ null target)}
         -> F1 s (Maybe (List Nat))
matchKMP pat target {prfpat} {prftarget} t =
  let matcher'   # t := matcher False pat [target] t
      Just matcher'' := matcher'
        | Nothing =>
            Nothing # t
    in Just matcher'' #t

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
||| indicesKMP "ABCABC" "ABCABCABC" => Just [0, 3]
|||
export
indicesKMP :  (pat : ByteString)
           -> (target : ByteString)
           -> {0 prfpat : So (not $ null pat)}
           -> {0 prftarget : So (not $ null target)}
           -> F1 s (Maybe (List Nat))
indicesKMP pat target {prfpat} {prftarget} t =
  let matcher'   # t := matcher True pat [target] t
      Just matcher'' := matcher'
        | Nothing =>
            Nothing # t
    in Just matcher'' # t

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
         -> F1 s (Maybe (ByteString, ByteString))
breakKMP pat target {prfpat} {prftarget} {prflength} t =
   let matcher'   # t := matcher False pat [target] t
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
breakAfterKMP :  (pat : ByteString)
              -> (target : ByteString)
              -> {0 prfpat : So (not $ null pat)}
              -> {0 prftarget : So (not $ null target)}
              -> {0 prflength : So ((length target) >= (length pat))}
              -> F1 s (Maybe (ByteString, ByteString))
breakAfterKMP pat target {prfpat} {prftarget} {prflength} t =
   let matcher'   # t := matcher False pat [target] t
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
                  -> F1 s (Maybe (List ByteString))
splitKeepFrontKMP pat target {prfpat} {prftarget} {prflength} t =
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
      let matcher'   # t := matcher False pat [(drop (length pat) target)] t
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
      let matcher'   # t := matcher False pat [target] t
          Just matcher'' := matcher'
            | Nothing =>
                Nothing # t
          (i :: _)       := matcher''
            | [] =>
                let final' := final :< target
                  in Just final' # t
          False          := i == Z
            | True =>
                assert_total (psSplitter pat target final t)
          final'         := final :< (take (cast {to=Nat} i) target)
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
                -> F1 s (Maybe (List ByteString))
splitKeepEndKMP pat target {prfpat} {prftarget} {prflength} t =
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
      let matcher'   # t := matcher False pat [target] t
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
             -> F1 s (Maybe (List ByteString))
splitDropKMP pat target {prfpat} {prftarget} {prflength} t =
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
      let matcher'   # t := matcher False pat [target] t
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
||| using the Knuth-Morris-Pratt matcher.
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
replaceKMP :  (pat : ByteString)
           -> (sub : ByteString)
           -> (target : ByteString)
           -> {0 prfpat : So (not $ null pat)}
           -> {0 prftarget : So (not $ null target)}
           -> {0 prflength : So ((length target) >= (length pat))}
           -> F1 s (Maybe (List ByteString))
replaceKMP pat sub target {prfpat} {prftarget} {prflength} t =
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
      let matcher'   # t := matcher False pat [target] t
          Just matcher'' := matcher'
            | Nothing =>
                Nothing # t
          (i :: _)       := matcher''
            | [] =>
                let final' := final :< target
                  in Just final' # t
          Z              := i
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
          final' := final :< sub
        in assert_total (replacer pat sub (drop (length pat) target) final') t
