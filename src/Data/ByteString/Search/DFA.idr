||| Fast deterministic finite automaton (DFA) search of ByteStrings
module Data.ByteString.Search.DFA

import Data.ByteString.Search.Internal.Utils
import Data.ByteString.Search.DFA.Internal

import Data.Array.Core
import Data.Array.Mutable
import Data.Bits
import Data.ByteString
import Data.Enum
import Data.Linear.Ref1
import Data.So

%hide Data.Buffer.Core.get
%hide Data.Buffer.Core.set

%default total

||| Search for occurrences of `pat` within `target` using a precomputed
||| deterministic finite automaton.
|||
||| When `overlap` is `True`, overlapping occurrences are retained. When it
||| is `False`, searching resumes after the end of each complete match.
|||
||| A single-byte pattern is handled separately using `elemIndex`, preserving
||| the behavior of the previous implementation.
|||
||| For patterns longer than one byte, the DFA is constructed once and the
||| target is scanned from left to right.
|||
||| State zero is handled specially so that target bytes which differ from
||| the first pattern byte do not require a DFA table lookup.
|||
||| Nonzero DFA states are represented by `DFAState`, which is an `Index`
||| carrying erased bounds evidence. Each call to `dfaTransition` therefore
||| accepts an already-valid state and returns another already-valid state.
||| No `tryNatToFin`, `tryIndex`, or equivalent DFA-table bounds check occurs
||| in the target-scanning hot path.
|||
private
matcher :  Bool
        -> ByteString
        -> ByteString
        -> F1 s (Maybe (List Nat))
matcher overlap pat target t =
  let patlen                      := length pat
      targetlen                   := length target
      False                       := patlen == S Z
        | True =>
            let Just patzero := index Z pat
                  | Nothing =>
                      Nothing # t
                Just headelem := elemIndex patzero target
                  | Nothing =>
                      Nothing # t
              in Just (headelem :: []) # t
      Just patzero                := index Z pat
        | Nothing =>
            Nothing # t
      dfa                     # t := automaton pat t
      Just dfa'                   := dfa
        | Nothing =>
            Nothing # t
      MkDFAutomaton stspace table := dfa'
      Just stateone               := tryIndex {r = stspace.states} 1
        | Nothing =>
            Nothing # t
      result                  # t := matchZero stspace Z Lin patlen targetlen patzero table stateone t
      Just result'                := result
        | Nothing =>
            Nothing # t
    in Just (result' <>> []) # t
  where
    mutual
      ||| Continue scanning while the DFA is in state zero.
      |||
      ||| State zero is treated specially because any byte other than the
      ||| first pattern byte necessarily leaves the automaton in state zero.
      ||| Such bytes can therefore be skipped without consulting the DFA
      ||| transition table.
      |||
      ||| When the first pattern byte is encountered, the matcher moves
      ||| directly to the prevalidated DFA state one and continues through
      ||| `matchState`.
      |||
      matchZero :  (stspace : DFAStateSpace)
                -> (idx : Nat)
                -> (final : SnocList Nat)
                -> (patlen : Nat)
                -> (targetlen : Nat)
                -> (patzero : Bits8)
                -> (dfa : DFATable s stspace.states)
                -> (stateone : DFAState stspace.states)
                -> F1 s (Maybe (SnocList Nat))
      matchZero stspace idx final patlen targetlen patzero dfa stateone t =
          let False     := idx == targetlen
                | True =>
                    Just final # t
              Just byte := index idx target
                | Nothing =>
                    Nothing # t
              nxtidx    := S idx
              False     := byte == patzero
                | True =>
                    assert_total (matchState stspace stateone nxtidx final patlen targetlen patzero dfa stateone t)
            in assert_total (matchZero stspace nxtidx final patlen targetlen patzero dfa stateone t)
      ||| Continue scanning from a nonzero DFA state.
      |||
      ||| The current state is represented by `DFAState`, so it is already
      ||| known to lie within the DFA's state space. `dfaTransition` computes
      ||| the flattened transition-table position from this bounded state and
      ||| the current input byte, performs the primitive array read, and
      ||| returns another bounded `DFAState`.
      |||
      ||| Consequently, the per-byte DFA lookup performs no explicit
      ||| `tryNatToFin`, `tryIndex`, or `Maybe`-based bounds validation.
      |||
      ||| When a complete match is found, overlapping searches resume one
      ||| byte after the start of the match, while non-overlapping searches
      ||| resume immediately after the matched pattern.
      |||
      ||| If a transition returns state zero, control returns to `matchZero`
      ||| so subsequent bytes can take advantage of the state-zero fast path.
      |||
      matchState :  (stspace : DFAStateSpace)
                 -> (state : DFAState stspace.states)
                 -> (idx : Nat)
                 -> (final : SnocList Nat)
                 -> (patlen : Nat)
                 -> (targetlen : Nat)
                 -> (patzero : Bits8)
                 -> (dfa : DFATable s stspace.states)
                 -> (stateone : DFAState stspace.states)
                 -> F1 s (Maybe (SnocList Nat))
      matchState stspace state idx final patlen targetlen patzero dfa stateone t =
          let False := idx == targetlen
                | True =>
                    Just final # t
              Just byte := index idx target
                | Nothing =>
                    Nothing # t
              nstate # t :=
                dfaTransition
                  {statesPrf = stspace.statesBounded}
                  dfa
                  state
                  byte
                  t
              nstateval :=
                dfaStateValue nstate
              nxtidx :=
                S idx
              False := nstateval == cast {to=Bits32} patlen
                | True =>
                    let matchidx :=
                          minus nxtidx patlen
                        final' :=
                          final :< matchidx
                        False := overlap
                          | True =>
                              assert_total (matchZero stspace (S matchidx) final' patlen targetlen patzero dfa stateone t)
                      in assert_total (matchZero stspace nxtidx final' patlen targetlen patzero dfa stateone t)
              False := nstateval == 0
                | True =>
                    assert_total (matchZero stspace nxtidx final patlen targetlen patzero dfa stateone t)
            in assert_total (matchState stspace nstate nxtidx final patlen targetlen patzero dfa stateone t)

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
||| matchDFA "AN" "ANPANMAN" => Just [0, 3, 6]
|||
export
matchDFA :  (pat : ByteString)
         -> (target : ByteString)
         -> {0 prfpat : So (not $ null pat)}
         -> {0 prftarget : So (not $ null target)}
         -> F1 s (Maybe (List Nat))
matchDFA pat target {prfpat} {prftarget} t =
  let matcher'   # t := matcher False pat target t
      Just matcher'' := matcher'
        | Nothing =>
            Nothing # t
    in Just matcher'' # t

||| Performs a string search on a `ByteString` utilizing a determinisitic-finite-automaton (DFA).
|||
||| This function finds all (0-based) indices (possibly overlapping)
||| of the non-empty pattern `ByteString` pat
||| within the non-empty target `ByteString`, using the deterministic-finite-automaton
||| (DFA) computed by `automaton`.
|||
||| Example:
|||
||| | pat      | target      |
||| | -------- | ----------- |
||| | "ABCABC" | "ABCABCABC" |
|||
||| | Start | Substring       | Match? | Explanation                                                      |
||| | ----- | --------------- | ------ | ---------------------------------------------------------------- |
||| | 0     | **"ABCABC"**ABC | Yes    | Full pattern matches starting at index 0.                        |
||| | 1     | A**"BCABCA"**BC | No     | Mismatch starts immediately after first letter.                  |
||| | 2     | AB**"CABCAA"**C | No     | Shift by suffix table → mismatch on 2nd char.                    |
||| | 3     | ABC**"ABC"**    | Yes    | Overlapping match starting at index 3 (because `"ABC"` repeats). |
||| 
||| indicesDFA "ABCABC" "ABCABCABC" => Just [0, 3]
|||
export
indicesDFA :  (pat : ByteString)
           -> (target : ByteString)
           -> {0 prfpat : So (not $ null pat)}
           -> {0 prftarget : So (not $ null target)}
           -> F1 s (Maybe (List Nat))
indicesDFA pat target {prfpat} {prftarget} t =
  let matcher'   # t := matcher True pat target t
      Just matcher'' := matcher'
        | Nothing =>
            Nothing # t
    in Just matcher'' # t

||| Splits a ByteString at the first match of pat in target.
|||
||| This function uses the deterministic-finite-automaton matcher (with overlap = False) to
||| locate the earliest occurrence of pat in target.  If the pattern is
||| found at index i, the pattern ByteString pat is split at that index,
||| returning the prefix and suffix as a pair (before, after).
|||
||| If the pattern does not occur in the target, (pat, empty) is returned.
||| In other words, the entire pattern becomes the “before” part and the
||| “after” part is an empty ByteString.
|||
export
breakDFA :  (pat : ByteString)
         -> (target : ByteString)
         -> {0 prfpat : So (not $ null pat)}
         -> {0 prftarget : So (not $ null target)}
         -> {0 prflength : So ((length target) >= (length pat))}
         -> F1 s (Maybe (ByteString, ByteString))
breakDFA pat target {prfpat} {prftarget} {prflength} t =
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
||| This function uses the deterministic-finite-automaton matcher (with overlap = False) to
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
breakAfterDFA :  (pat : ByteString)
              -> (target : ByteString)
              -> {0 prfpat : So (not $ null pat)}
              -> {0 prftarget : So (not $ null target)}
              -> {0 prflength : So ((length target) >= (length pat))}
              -> F1 s (Maybe (ByteString, ByteString))
breakAfterDFA pat target {prfpat} {prftarget} {prflength} t =
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
||| (using the deterministic-finite-automaton matcher with overlap = False).  Each time a
||| match is found at index i, the prefix of pat up to i + length pat
||| is emitted as the next chunk, and the function continues processing the
||| remaining suffix of pat.
|||
||| Unlike breakDFA or breakAfterDFA, this function performs repeated
||| splitting until the entire pattern has been consumed, producing a
||| list of ByteStrings.
|||
export
splitKeepFrontDFA :  (pat : ByteString)
                  -> (target : ByteString)
                  -> {0 prfpat : So (not $ null pat)}
                  -> {0 prftarget : So (not $ null target)}
                  -> {0 prflength : So ((length target) >= (length pat))}
                  -> F1 s (Maybe (List ByteString))
splitKeepFrontDFA pat target {prfpat} {prftarget} {prflength} t =
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
||| (using the deterministic-finite-automaton matcher with overlap = False).  Each time a
||| match is found at index i, the next chunk emitted is the prefix of
||| target of length i + length pat, which includes the entire matched
||| occurrence of pat at its end.
|||
||| After emitting this chunk, the function continues splitting the
||| remainder of target until all input has been consumed.
|||
||| Unlike splitKeepFrontDFA, which keeps the matched prefix of pat
||| at the front of each chunk, splitKeepEndDFA ensures the match
||| appears at the end of each chunk.
|||
||| If pat does not occur in target, the result is a singleton list
||| containing the original target.
|||
export
splitKeepEndDFA :  (pat : ByteString)
                -> (target : ByteString)
                -> {0 prfpat : So (not $ null pat)}
                -> {0 prftarget : So (not $ null target)}
                -> {0 prflength : So ((length target) >= (length pat))}
                -> F1 s (Maybe (List ByteString))
splitKeepEndDFA pat target {prfpat} {prftarget} {prflength} t =
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
||| (using the deterministic-finite-automaton matcher with overlap = False).  Each time a
||| match is found at index i, the prefix of target of length i
||| (that is, the portion preceding the match) is emitted as the next
||| chunk.  The matched substring itself is not included.
|||
||| After emitting this prefix, the function continues splitting the
||| remainder of target, skipping over the full match of length
||| i + length pat.  This process continues until the entire target
||| has been consumed.
|||
||| Unlike splitKeepFrontDFA and splitKeepEndDFA, which include the
||| matched pattern in each emitted chunk, splitDropKMP removes all
||| occurrences of pat from the output.
|||
||| If pat does not occur in target, the result is a singleton list
||| containing the original target.
|||
export
splitDropDFA :  (pat : ByteString)
             -> (target : ByteString)
             -> {0 prfpat : So (not $ null pat)}
             -> {0 prftarget : So (not $ null target)}
             -> {0 prflength : So ((length target) >= (length pat))}
             -> F1 s (Maybe (List ByteString))
splitDropDFA pat target {prfpat} {prftarget} {prflength} t =
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
          final'         := final :< (take (cast {to=Nat} i) target)
        in assert_total (splitter pat (drop length' target) final' t)

||| Replaces all non-overlapping occurrences of a pattern in a ByteString
||| using the deterministic-finite-automaton matcher.
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
replaceDFA :  (pat : ByteString)
           -> (sub : ByteString)
           -> (target : ByteString)
           -> {0 prfpat : So (not $ null pat)}
           -> {0 prftarget : So (not $ null target)}
           -> {0 prflength : So ((length target) >= (length pat))}
           -> F1 s (Maybe (List ByteString))
replaceDFA pat sub target {prfpat} {prftarget} {prflength} t =
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
          final'         := final :< sub
        in assert_total (replacer pat sub (drop (length pat) target) final') t
