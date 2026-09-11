# Fast searching, replacing, and splitting of ByteStrings

This is a [bytestring](https://github.com/stefan-hoeck/idris2-bytestring)-searching library that provides [array](https://github.com/stefan-hoeck/idris2-array)-backed implementations of the [Boyer-Moore](https://en.wikipedia.org/wiki/Boyer%E2%80%93Moore_string-search_algorithm) algorithm,
[Knuth-Morris-Pratt](https://en.wikipedia.org/wiki/Knuth%E2%80%93Morris%E2%80%93Pratt_algorithm) algorithm,
and a [deterministic-finite-automaton](https://en.wikipedia.org/wiki/Deterministic_finite_automaton) (DFA) based algorithm.

## String-searching algorithms

String-searching (or string-matching) is the problem of finding occurrence(s) of a [_pattern_](https://xlinux.nist.gov/dads/HTML/pattern.html) string
within another [_string_](https://xlinux.nist.gov/dads/HTML/string.html) or body of text (see the National Institute of Standards and Technology’s (NIST) Dictionary of Algorithms and Data Structures (DADS) article for [string-matching](https://xlinux.nist.gov/dads/HTML/stringMatching.html)).

String-searching algorithms are used in many real-world applications, such as:

- [Sequence alignment](https://en.wikipedia.org/wiki/Sequence_alignment "Sequence alignment")
- [Graph matching](https://en.wikipedia.org/wiki/Graph_matching "Graph matching")
- [Pattern matching](https://en.wikipedia.org/wiki/Pattern_matching "Pattern matching")
- [Compressed pattern matching](https://en.wikipedia.org/wiki/Compressed_pattern_matching "Compressed pattern matching")
- [Matching wildcards](https://en.wikipedia.org/wiki/Matching_wildcards "Matching wildcards")
- [Approximate string matching](https://en.wikipedia.org/wiki/Approximate_string_matching "Approximate string matching")
- [Full-text search](https://en.wikipedia.org/wiki/Full-text_search "Full-text search")

### Boyer-Moore algorithm

The [Boyer-Moore](https://en.wikipedia.org/wiki/Boyer%E2%80%93Moore_string-search_algorithm) algorithm,
developed in 1977 by [Robert S. Boyer](https://en.wikipedia.org/wiki/Robert_S._Boyer) and [J. Strother Moore](https://en.wikipedia.org/wiki/J_Strother_Moore), is considered the standard by which all other string-searching algorithms are bench-marked.
The key idea of this algorithm is that it pre-computes the shifts of bad-characters and good-suffixes.

#### Bad Character Rule

The bad-character rule considers the character in the text (T) at which the comparison process failed (assuming such a failure occurred).
The next occurrence of that character to the left in the pattern (P) is found, and a shift which brings that occurrence in line with the mismatched occurrence in T is proposed.
If the mismatched character does not occur to the left in P, a shift is proposed that moves the entirety of P past the point of mismatch.

This library pre-computes the bad-character rule using the `occurrences` function (found in `Data.ByteString.Search.Internal.Utils` module):

```idris
occurrences :  (bs : ByteString)
            -> {0 prf : So (not $ null bs)}
            -> F1 s (Maybe (OccurrenceTable s))
occurrences bs t =
  let arr # t := newOccurrenceTable t
    in go Z (length bs) arr t
  where
    go :  (i : Nat)
      -> (patend : Nat)
      -> OccurrenceTable s
      -> F1 s (Maybe (OccurrenceTable s))
    go i patend arr t =
      let False     := S i >= patend
            | True =>
                Just arr # t
          Just byte := index i bs
            | Nothing =>
                Nothing # t
          ()    # t := setOccurrence arr byte (negate $ cast {to=Int} i) t
       in assert_total (go (S i) patend arr t)
```

`occurrences` answers the following question:

"If I see character X at position i and mismatch, how far can I slide the pattern?"

It accomplishes this by:

- Storing the negative `index` of the rightmost occurrence, which is important as it allows computing shift with a single addition.
- Defaulting to `1` for unknown characters, which allows the algorithm to slide pattern completely past them.
  - This is done early on when we create the array initially, `marray1 256 (the Int 1) t`.
- Ignoring the last pattern index, which prevents zero-shift infinite loops.

##### Example - occurrences

Given the following pattern "ANPANMAN":

```text
0 1 2 3 4 5 6 7
A N P A N M A N
```

`occurrences` stops at index `6`, and produces the following:

`[(65, -6), (77, -5), (78, -4), (80, -2)]`

The first element of tuple is the ASCII code for the character (`A` === `65`, `M` === `77`, `N` === `78`, `P` === `80`).

Which can be summarized with the following table:

| Char    | Last stored index | Table value |
| ------- | ----------------- | ----------- |
| A       | 6                 | -6          |
| M       | 5                 | -5          |
| N       | 4                 | -4          |
| P       | 2                 | -2          |
| [^AMNP] | N/A               | 1           |


##### Summary

- If the target has many characters not in the pattern, you'll get large shifts, which is fast since you can skip a great amount of characters/comparisons.
- If the target contains lots of characters from the pattern near its end, you'll get small shifts, which is slower since the magnitude of the shifts is far small in comparison.

The above illustrates why it's important to keep in mind that Boyer–Moore is very sensitive to character distribution, unlike the DFA-based algorithm (which we'll dive into later).

#### Good Suffix Rule

The good suffix rule is another pre-processing that occurs within the Boyer-Moore algorithm, which is slightly more complex than the above bad character rule:

The Boyer-Moore Wikipedia [article](https://en.wikipedia.org/wiki/Boyer%E2%80%93Moore_string-search_algorithm) gives a nice description:
> Suppose for a given alignment of _**P**_ and _**T**_, a substring _**t**_ of _**T**_ matches a suffix of _**P**_ and suppose _**t**_ is the largest such substring for the given alignment.
>
> 1. Then find, if it exists, the right-most copy _**t′**_ of _**t**_ in _**P**_ such that _**t′**_ is not a suffix of _**P**_ and the character to the left of _**t′**_ in _**P**_ differs from the character to the left of _**t**_ in _**P**_. Shift _**P**_ to the right so that substring _**t′**_ in _**P**_ aligns with substring _**t**_ in _**T**_.
> 2. If _**t′**_ does not exist, then shift the left end of _**P**_ to the right by the least amount (past the left end of _**t**_ in _**T**_) so that a prefix of the shifted pattern matches a suffix of _**t**_ in _**T**_. This includes cases where _**t**_ is an exact match of _**P**_.
> 3. If no such shift is possible, then shift _**P**_ by **m** (length of P) places to the right.

This library pre-computes the good-suffix rule using the `suffixLengths` and the `suffixShifts` functions (found in `Data.ByteString.Search.Internal.Utils` module).

Let's focus on the `suffixLengths` function first:

```idris
suffixLengths :  (bs : ByteString)
              -> {0 prf : So (not $ null bs)}
              -> F1 s (Maybe (BMPatternTable s))
suffixLengths bs {prf} t =
  let Just stspace := bmPatternSpace bs {prf = prf}
        | Nothing =>
            Nothing # t
      arr      # t := newBMIntTableWith {size = stspace.size} 0 t
      lastidxnat   := minus (length bs) 1
      Just lastidx := toPatternIndex stspace lastidxnat
        | Nothing =>
            Nothing # t
      ()       # t := bmSet arr lastidx (cast {to=Int} $ length bs) t
      arr'     # t := noSuffix stspace (cast {to=Int} $ minus (length bs) 2) arr t
      Just arr''   := arr'
        | Nothing =>
            Nothing # t
    in Just (MkBMPatternTable stspace arr'') # t
  where
    dec :  (diff : Int)
        -> (j : Int)
        -> F1 s (Maybe Int)
    dec diff j t =
      let False        := j < 0
            | True =>
                Just j # t
          Just jbyte   := index (cast {to=Nat} j) bs
            | Nothing =>
                Nothing # t
          Just shifted := index (cast {to=Nat} (j + diff)) bs
            | Nothing =>
                Nothing # t
          False        := jbyte /= shifted
            | True =>
                Just j # t
        in assert_total (dec diff (j - 1) t)
    mutual
      suffixLoop :  (stspace : BMPatternSpace)
                 -> (pre : Int)
                 -> (end : Int)
                 -> (idx : Int)
                 -> (arr : BMIntTable s stspace.size)
                 -> F1 s (Maybe (BMIntTable s stspace.size))
      suffixLoop _       _   _   0   arr t =
        Just arr # t
      suffixLoop stspace pre end idx arr t =
        let True         := pre < idx
              | False =>
                  noSuffix stspace idx arr t
            Just idxbyte := index (cast {to=Nat} idx) bs
              | Nothing =>
                  Nothing # t
            Just endbyte := index (minus (length bs) 1) bs
              | Nothing =>
                  Nothing # t
            Just idxpos := toPatternIndex stspace (cast {to=Nat} idx)
              | Nothing =>
                  Nothing # t
            False       := idxbyte /= endbyte
              | True =>
                  let () # t := bmSet arr idxpos 0 t
                    in assert_total (suffixLoop stspace pre (end - 1) (idx - 1) arr t)
            Just endpos := toPatternIndex stspace (cast {to=Nat} end)
              | Nothing =>
                  Nothing # t
            prevs   # t := bmGet arr endpos t
            False       := (pre + prevs) < idx
              | True =>
                  let () # t := bmSet arr idxpos prevs t
                    in assert_total (suffixLoop stspace pre (end - 1) (idx - 1) arr t)
            pri     # t := dec (cast {to=Int} (minus (length bs) (cast {to=Nat} idx))) pre t
            Just pri'   := pri
              | Nothing =>
                  Nothing # t
            ()      # t := bmSet arr idxpos (idx - pri') t
          in assert_total (suffixLoop stspace pri' (cast {to=Int} $ minus (length bs) 2) (idx - 1) arr t)
      noSuffix :  (stspace : BMPatternSpace)
               -> (i : Int)
               -> (arr : BMIntTable s stspace.size)
               -> F1 s (Maybe (BMIntTable s stspace.size))
      noSuffix _       0 arr t =
        Just arr # t
      noSuffix stspace i arr t =
        let Just patati   := index (cast {to=Nat} i) bs
              | Nothing =>
                  Nothing # t
            Just patatend := index (minus (length bs) 1) bs
              | Nothing =>
                  Nothing # t
            Just ipos     := toPatternIndex stspace (cast {to=Nat} i)
              | Nothing =>
                  Nothing # t
            True          := patati == patatend
              | False =>
                  let () # t := bmSet arr ipos 0 t
                    in assert_total (noSuffix stspace (i - 1) arr t)
            diff             := cast {to=Int} (minus (length bs) 1) - i
            nexti            := i - 1
            previ        # t := dec diff nexti t
            Just previ'      := previ
              | Nothing =>
                  Nothing # t
            False            := previ' == nexti
              | True =>
                  let () # t := bmSet arr ipos 1 t
                    in assert_total (noSuffix stspace nexti arr t)
            ()           # t := bmSet arr ipos (i - previ') t
          in assert_total (suffixLoop stspace previ' (cast {to=Int} $ minus (length bs) 2) nexti arr t)
```

`suffixLengths` computes the following:

For each position i in the pattern, `suffixLengths[i]` tells you how long a suffix of `P[0..i]` matches the suffix of the full pattern.

##### Example - suffixLengths

Given the following pattern "ANPANMAN":

```text
0 1 2 3 4 5 6 7
A N P A N M A N
```

The suffixes of the pattern are:

```text
"" 
"N"
"AN"
"MAN"
"NMAN"
"ANMAN"
"PANMAN"
"NPANMAN"
"ANPANMAN"
```

`suffixLengths` produces the following:

`[0, 2, 0, 0, 2, 0, 0, 8]`

Which can be summarized with the following table:

| i | pat[i] | matches pattern end? | diff = patend - i | nexti = i-1 | previ (dec diff nexti) | array[i] |
| - | ------ | -------------------- | ----------------- | ----------- | ---------------------- | -------- |
| 0 |    A   |          No          |         -         |      -      |            -           |   0      |
| 1 |    N   |          Yes         |         6         |      0      |           -1           |   2      |
| 2 |    P   |          No          |         -         |      -      |            -           |   0      |
| 3 |    A   |          No          |         -         |      -      |            -           |   0      |
| 4 |    N   |          Yes         |         3         |      3      |            2           |   2      |
| 5 |    M   |          No          |         -         |      -      |            -           |   0      |
| 6 |    A   |          No          |         -         |      -      |            -           |   0      |
| 7 |    N   |       - (last)       |         -         |      -      |            -           |   8      |

`suffixLengths[i]`  answers:

Starting at i, how many characters at the end match the pattern’s end?

`noSuffix` is the first pass from the end of the pattern to the beginning of the pattern.

When `P[i] == P[last]`, it tries to grow a suffix, and continues until mismatch.  This gives the longest suffix match anchored at i.

```text
set arr[i] = i - previ
```

The above stores the number of characters backwards matched.

`suffixLoop` makes `suffixLengths` linear time instead of quadratic, it reuses previously computed suffix values if possible.

Now, we can dive into the `suffixShifts` function:

```idris
suffixShifts :  (bs : ByteString)
             -> {0 prf : So (not $ null bs)}
             -> F1 s (Maybe (BMPatternTable s))
suffixShifts bs {prf} t =
  let suff                              # t := suffixLengths bs {prf = prf} t
      Just (MkBMPatternTable stspace suff') := suff
        | Nothing =>
            Nothing # t
      arr                               # t := newBMIntTableWith {size = stspace.size} (cast {to=Int} $ length bs) t
      arr'                              # t := prefixShift stspace (cast {to=Int} $ minus (length bs) 2) 0 suff' arr t
      Just arr''                            := arr'
        | Nothing =>
            Nothing # t
      arr'''                            # t := suffixShift stspace 0 suff' arr'' t
      Just arr''''                          := arr'''
        | Nothing =>
            Nothing # t
    in Just (MkBMPatternTable stspace arr'''') # t
  where
    fillToShift :  (stspace : BMPatternSpace)
                -> (i : Int)
                -> (shift : Int)
                -> (arr : BMIntTable s stspace.size)
                -> F1 s (Maybe (BMIntTable s stspace.size))
    fillToShift stspace i shift arr t =
      let False     := i == shift
            | True =>
                Just arr # t
          Just ipos := toPatternIndex stspace (cast {to=Nat} i)
            | Nothing =>
                Nothing # t
          ()    # t := bmSet arr ipos shift t
        in assert_total (fillToShift stspace (i + 1) shift arr t)
    prefixShift :  (stspace : BMPatternSpace)
                -> (idx : Int)
                -> (j : Int)
                -> (suff : BMIntTable s stspace.size)
                -> (arr : BMIntTable s stspace.size)
                -> F1 s (Maybe (BMIntTable s stspace.size))
    prefixShift stspace idx j suff arr t =
      let False       := idx < 0
            | True =>
                Just arr # t
          Just idxpos := toPatternIndex stspace (cast {to=Nat} idx)
            | Nothing =>
                Nothing # t
          idxval  # t := bmGet suff idxpos t
          True        := idxval == idx + 1
            | False =>
                assert_total (prefixShift stspace (idx - 1) j suff arr t)
          shift       := cast {to=Int} (minus (length bs) 1) - idx
          arr'    # t := fillToShift stspace j shift arr t
          Just arr''  := arr'
            | Nothing =>
                Nothing # t
        in assert_total (prefixShift stspace (idx - 1) shift suff arr'' t)
    suffixShift :  (stspace : BMPatternSpace)
                -> (idx : Int)
                -> (suff : BMIntTable s stspace.size)
                -> (arr : BMIntTable s stspace.size)
                -> F1 s (Maybe (BMIntTable s stspace.size))
    suffixShift stspace idx suff arr t =
      let patend         := cast {to=Int} (minus (length bs) 1)
          False          := idx >= patend
            | True =>
                Just arr # t
          Just idxpos    := toPatternIndex stspace (cast {to=Nat} idx)
            | Nothing =>
                Nothing # t
          sufflen    # t := bmGet suff idxpos t
          target         := patend - sufflen
          Just targetpos := toPatternIndex stspace (cast {to=Nat} target)
            | Nothing =>
                Nothing # t
          value          := patend - idx
          ()         # t := bmSet arr targetpos value t
        in assert_total (suffixShift stspace (idx + 1) suff arr t)
```

`suffixShifts` uses the lengths from `suffixLengths` to compute the actual suffix shifts.

`prefixShifts` shifts the pattern so that prefix lines up with the suffix if a suffix of the matched portion is also a prefix of the pattern.

`suffixShift` shifts the pattern so that the next instance of that suffix aligns if a mismatch occurred at index `i` and the suffix length is `s`, which looks like `shift = (pattern length - 1) - i`.

##### Example - suffixShifts

Given the following pattern "ANPANMAN":

`suffixShifts` produces the following:

`[6, 6, 6, 6, 6, 3, 8, 1]`

Which can be summarized with the following table:

| Index | suff[idx] | target = patend - suff[i] | value = patend - i | array after write        |
| ----- | --------- | ------------------------- | ------------------ | ------------------------ |
|   0   |         0 |                 7 - 0 = 7 |          7 - 0 = 7 | [6, 6, 6, 6, 6, 6, 8, 7] |
|   1   |         2 |                 7 - 2 = 5 |          7 - 1 = 6 | [6, 6, 6, 6, 6, 6, 8, 7] |
|   2   |         0 |                         7 |          7 - 2 = 5 | [6, 6, 6, 6, 6, 6, 8, 5] |
|   3   |         0 |                         7 |          7 - 3 = 4 | [6, 6, 6, 6, 6, 6, 8, 4] |
|   4   |         2 |                 7 - 2 = 5 |          7 - 4 = 3 | [6, 6, 6, 6, 6, 3, 8, 4] |
|   5   |         0 |                         7 |          7 - 5 = 2 | [6, 6, 6, 6, 6, 3, 8, 2] |
|   6   |         0 |                         7 |          7 - 6 = 1 | [6, 6, 6, 6, 6, 3, 8, 1] |

### DFA algorithm

A DFA is a [finite-state machine](https://en.wikipedia.org/wiki/Finite-state_machine "Finite-state machine") that accepts or rejects
a given [string](https://en.wikipedia.org/wiki/String_(computer_science) "String (computer science)") of symbols, by running through a state sequence uniquely determined by the string.

#### Creating the DFA via automaton

Given a pattern `P` of length `m` (length of `P`) and an alphabet `Σ` (bytes = 256 values), the goal is to build a DFA using the `automaton` function found in the `Data.ByteString.Search.Internal.Utils` module:

```idris
automaton :  (bs : ByteString)
          -> F1 s (Maybe (DFAutomaton s))
automaton bs t =
   let bord                          # t := kmpBorders bs t
       Just (MkKMPBorders stspace bord') := bord
         | Nothing =>
             Nothing # t
       arr                           # t := newDFATable {states = stspace.states} {statesPrf = stspace.statesBounded} t
       result                        # t := go stspace Z arr bord' t
       Just result'                      := result
         | Nothing =>
             Nothing # t
     in Just (MkDFAutomaton stspace result') # t
  where
    fillState :  (space : DFAStateSpace)
              -> (state : DFAState space.states)
              -> (byte : Bits8)
              -> (patbyte : Maybe Bits8)
              -> (bordcur : DFAState space.states)
              -> (arr : DFATable s space.states)
              -> F1 s (Maybe (DFATable s space.states))
    fillState space state byte patbyte bordcur arr t =
      let stateval      := dfaStateValue state
          Just patbyte' := patbyte
            | Nothing =>
                let False        := stateval == 0
                      | True =>
                          let zero   := zeroDFAState space
                              () # t := setDFATransition {statesPrf = space.statesBounded} arr state byte zero t
                              True   := byte == 0
                                | False =>
                                    assert_total (fillState space state (byte - 1) patbyte bordcur arr t)
                            in Just arr # t
                    bordcur' # t := dfaTransition {statesPrf = space.statesBounded} arr bordcur byte t
                    ()       # t := setDFATransition {statesPrf = space.statesBounded} arr state byte bordcur' t
                    True         := byte == 0
                      | False =>
                          assert_total (fillState space state (byte - 1) patbyte bordcur' arr t)
                  in Just arr # t
          False         := byte == patbyte'
            | True =>
                let Just next := toDFAState space (S $ cast stateval)
                      | Nothing =>
                          Nothing # t
                    ()    # t := setDFATransition {statesPrf = space.statesBounded} arr state byte next t
                    True      := byte == 0
                      | False =>
                          assert_total (fillState space state (byte - 1) patbyte bordcur arr t)
                  in Just arr # t
          False         := stateval == 0
            | True =>
                let zero   := zeroDFAState space
                    () # t := setDFATransition {statesPrf = space.statesBounded} arr state byte zero t
                    True   := byte == 0
                      | False =>
                          assert_total (fillState space state (byte - 1) patbyte bordcur arr t)
                  in Just arr # t
          bordcur'  # t := dfaTransition {statesPrf = space.statesBounded} arr bordcur byte t
          ()        # t := setDFATransition {statesPrf = space.statesBounded} arr state byte bordcur' t
          True          := byte == 0
            | False =>
                assert_total (fillState space state (byte - 1) patbyte bordcur' arr t)
        in Just arr # t
    ||| Construct the transition rows for each DFA state.
    |||
    ||| The KMP border table and DFA transition table share the same bounded
    ||| state space, so border values can be consumed directly as DFA states
    ||| without any intermediate `Nat` or `Fin` conversion.
    |||
    go :  (stspace : DFAStateSpace)
       -> (state : Nat)
       -> (arr : DFATable s stspace.states)
       -> (bord : KMPBorderTable s stspace.states)
       -> F1 s (Maybe (DFATable s stspace.states))
    go stspace state arr bord t =
      let False          := state > length bs
            | True =>
                Just arr # t
          Just state' := toDFAState stspace state
            | Nothing =>
                Nothing # t
          bordcur # t := kmpBorder bord state' t
          patbyte        := index state bs
          arr'       # t := fillState stspace state' 255 patbyte bordcur arr t
          Just arr''     := arr'
            | Nothing =>
                Nothing # t
       in assert_total (go stspace (S state) arr'' bord t)
```
The automaton is:

> A table `δ(state, byte) → nextState`

Where:

- `state` = how many characters of the pattern we have matched so far (`0 … m`)  
- `byte` = next input character (`0 … 255`)
- `nextState` = the new amount of the pattern matched after seeing that byte

Early on in the `automaton` function, we create an `MArray` of `(m + 1) states * 256 bytes` size:

```idris
MArray s (mult (plus (length bs) 1) 256) Nat
```

Which flattens `(state, byte)` into a single array.

The `go` and `fillState` nested functions build the DFA row by row, and then the `loop` nested function loops over every byte value from 0 -> 255.

Keep in mind, the KMP borders are already pre-computed via the `kmpBorders` function (more on this later). The array generated by `kmpBorders` encodes all valid fallback transitions, avoiding expensive back-tracking upon mismatches.

#### Example - automaton

Given the following pattern "ANPANMAN":

`automaton` produces the following:

`[(65, 1), (321, 1), (334, 2), (577, 1), (592, 3), (833, 4), (1089, 1), (1102, 5), (1345, 1), (1357, 6), (1601, 7), (1857, 1), (1870, 8), (2113, 1)]`

Which can be summarized with the following table:

| Flat index | State | Char code | Char | Meaning       |
| ---------- | ----- | --------- | ---- | ------------- |
| 65         | 0     | 65        | 'A'  | δ(0, 'A') = 1 |
| 321        | 1     | 65        | 'A'  | δ(1, 'A') = 1 |
| 334        | 1     | 78        | 'N'  | δ(1, 'N') = 2 |
| 577        | 2     | 65        | 'A'  | δ(2, 'A') = 1 |
| 592        | 2     | 80        | 'P'  | δ(2, 'P') = 3 |
| 833        | 3     | 65        | 'A'  | δ(3, 'A') = 4 |
| 1089       | 4     | 65        | 'A'  | δ(4, 'A') = 1 |
| 1102       | 4     | 78        | 'N'  | δ(4, 'N') = 5 |
| 1345       | 5     | 65        | 'A'  | δ(5, 'A') = 1 |
| 1357       | 5     | 77        | 'M'  | δ(5, 'M') = 6 |
| 1601       | 6     | 65        | 'A'  | δ(6, 'A') = 7 |
| 1857       | 7     | 65        | 'A'  | δ(7, 'A') = 1 |
| 1870       | 7     | 78        | 'N'  | δ(7, 'N') = 8 |
| 2113       | 8     | 65        | 'A'  | δ(8, 'A') = 1 |

### Knuth-Morris-Pratt algorithm

The [Knuth-Morris-Pratt](https://en.wikipedia.org/wiki/Knuth%E2%80%93Morris%E2%80%93Pratt_algorithm) (KMP) algorithm was developed almost simultaneously
(within weeks of each other) by [James H. Morris](https://en.wikipedia.org/wiki/James_H._Morris "James H. Morris") and [Donald Knuth](https://en.wikipedia.org/wiki/Donald_Knuth "Donald Knuth").
Morris and [Vaughan Pratt](https://en.wikipedia.org/wiki/Vaughan_Pratt "Vaughan Pratt") formally published it in a technical report in 1970.

The KMP algorithm is a linear-time string-searching algorithm that finds all occurrences of a pattern within a text without re-examining characters that have already been matched.

Instead of restarting the search from the beginning of the pattern after a mismatch, KMP uses a pre-computed prefix table (also called a failure function or partial match table) to determine how far the pattern can be shifted while preserving previously matched characters.

This library pre-computes the table rule using the `kmpBorders` function (found in `Data.ByteString.Search.Internal.Utils` module):

```idris
kmpBorders :  (bs : ByteString)
           -> F1 s (Maybe (KMPBorders s))
kmpBorders bs t =
  let Just stspace := dfaStateSpace bs
        | Nothing =>
            Nothing # t
      arr # t      := newKMPBorderTable {states = stspace.states} t
      zero         : DFAState stspace.states
      zero         := I 0 {prf = stspace.statesPositive}
      ()       # t := setKMPBorder arr zero zero t
      Just one     := nextDFAState stspace zero
        | Nothing =>
            Nothing # t
    in go stspace one zero arr t
  where
    mutual
      ||| Continue resolving the border for the current pattern position.
      |||
      ||| On a matching pattern byte, both the current pattern position and
      ||| border position advance by one. On a mismatch, the previous border
      ||| value is read directly from the bounded KMP border table.
      |||
      advance :  (stspace : DFAStateSpace)
              -> (i : DFAState stspace.states)
              -> (j : DFAState stspace.states)
              -> (wi : Bits8)
              -> (arr : KMPBorderTable s stspace.states)
              -> F1 s (Maybe (KMPBorders s))
      advance stspace i j wi arr t =
        let jidx    := cast {to=Nat} (dfaStateValue j)
            Just wj := index jidx bs
              | Nothing =>
                  Nothing # t
            False   := wi == wj
              | True =>
                  let Just i' := nextDFAState stspace i
                        | Nothing =>
                            Nothing # t
                      Just j' := nextDFAState stspace j
                        | Nothing =>
                            Nothing # t
                      () # t := setKMPBorder arr i' j' t
                    in assert_total (go stspace i' j' arr t)
            False   := dfaStateValue j == 0
              | True =>
                  let Just i' := nextDFAState stspace i
                        | Nothing =>
                            Nothing # t
                      zero    : DFAState stspace.states
                      zero    := I 0 {prf = stspace.statesPositive}
                      ()  # t := setKMPBorder arr i' zero t
                    in assert_total (go stspace i' zero arr t)
            j'  # t := kmpBorder arr j t
          in assert_total (advance stspace i j' wi arr t)
      ||| Process the next pattern position while constructing the KMP border
      ||| table.
      |||
      ||| `i` and `j` are already valid DFA states, so border-table indexing
      ||| requires no dynamic conversion to `Fin`.
      |||
      go :  (stspace : DFAStateSpace)
         -> (i : DFAState stspace.states)
         -> (j : DFAState stspace.states)
         -> (arr : KMPBorderTable s stspace.states)
         -> F1 s (Maybe (KMPBorders s))
      go stspace i j arr t =
        let iidx    := cast {to=Nat} (dfaStateValue i)
            False   := iidx == length bs
              | True =>
                  Just (MkKMPBorders stspace arr) # t
            Just wi := index iidx bs
              | Nothing =>
                  Nothing # t
         in assert_total (advance stspace i j wi arr t)
```

The table helps efficiently skip positions in the pattern during sub-string search, while descending from longer prefixes to shorter ones.

#### Example - kmpBorders

Given the following pattern "ANPANMAN":

`kmpBorders` produces the following:

`[0, 0, 0, 0, 1, 2, 0, 1, 2]`

Which can be summarized with the following table:

| Index | Prefixes   | Borders | Explanation            |
| ----- | ---------- | ------- | ---------------------- |
| 0     | ""         | 0       | no border              |
| 1     | "A"        | 0       | "A" <-> no border      |
| 2     | "AN"       | 0       | "AN" <-> no border     |
| 3     | "ANP"      | 0       | "ANP" <-> no border    |
| 4     | "ANPA"     | 1       | "ANPA" <-> "A"         |
| 5     | "ANPAN"    | 2       | "ANPAN" <-> "AN"       |
| 6     | "ANPANM"   | 0       | "ANPANM" <-> no border |
| 7     | "ANPANMA"  | 1       | "ANPANMA" <-> "A"      |
| 8     | "ANPANMAN" | 2       | "ANPANMAN" <-> "AN"    |

#### How KMP uses the suffix-oriented table

Assume that `j` characters have been matched, and then a mismatch occurs.

Instead of the following:

```text
textIndex = textIndex - j + 1

j = 0 
```

We can simply do:

```text
j = kmpBorders[j - 1] 
```

This allows continuation from the already-known partial match.

This is what gives KMP its linear time, since each character in the text is processed at most once.

### Summary of algorithms

The following table (credit to [wikipedia](https://en.wikipedia.org/wiki/String-searching_algorithm)) summarizes the time (pre-processing and actual matching) and space complexities of the various algorithms this library provides (along with the Naïve algorithm for comparison):

| Algorithm          | Pre-processing | Matching                       | Space |
| ------------------ | -------------- | ------------------------------ | ----- |
| Naïve              | none           | Θ(n+m) in average,  O(mn)      | none  |
| Boyer-Moore        | Θ(m + k)       | O(n/m) at best, O(mn) at worst | Θ(k)  |
| DFA                | Θ(km)          | Θ(n)                           | Θ(km) |
| Knuth-Morris-Pratt | Θ(m)           | Θ(n)                           | Θ(m)  |

```text
m <-> length of pattern being searched for
n <-> length of text being searched across
k <-> |Σ| is the size of the alphabet
```

## Inter-language Benchmarks

| Benchmark              | Versus  | Link                                                                                                |
| ---------------------- | ------- | --------------------------------------------------------------------------------------------------- |
| Streaming from a file  | Haskell | [link](https://github.com/Matthew-Mosior/streaming-benchmarks/blob/main/string-searching/README.md) |
