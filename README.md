# Fast searching, replacing, and splitting of ByteStrings

This is a [ByteString](https://github.com/stefan-hoeck/idris2-bytestring)-searching library that provides [array](https://github.com/stefan-hoeck/idris2-array)-backed implementations of the [Boyer-Moore](https://en.wikipedia.org/wiki/Boyer%E2%80%93Moore_string-search_algorithm) algorithm,
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
developed in 1977 by Robert S. Boyer and J. Strother Moore, is considered the standard by which all other string-searching algorithms are bench-marked.
The key idea of this algorithm is that it pre-computes the shifts of bad-characters and good-suffixes.

#### Bad Character Rule

The bad-character rule considers the character in the text (T) at which the comparison process failed (assuming such a failure occurred).
The next occurrence of that character to the left in the pattern (P) is found, and a shift which brings that occurrence in line with the mismatched occurrence in T is proposed.
If the mismatched character does not occur to the left in P, a shift is proposed that moves the entirety of P past the point of mismatch.

This library pre-computes the bad-character rule using the `occurrences` function (found in `Data.ByteString.Search.Internal.Utils` module):

```idris
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
```

`occurrences` answers the following question:

"If I see character X at position i and mismatch, how far can I slide the pattern?"

It accomplishes this by storing:

-   Storing he negative `index` of the rightmost occurrence, which is important as it allows computing shift with a single addition.
-   Defaulting to `1` for unknown characters, which allows the algorithm to slide pattern completely past them.
    -  This is done early on when we create the array initially, `marray1 256 (the Int 1) t`.
-  Ignoring the last pattern index, which prevents zero-shift infinite loops.

##### Example

Given the following pattern "ANPANMAN":

```
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

-   If the target has many characters not in the pattern, you'll get large shifts, which is fast since you can skip a great amount of characters/comparisons.
-   If the target contains lots of characters from the pattern near its end, you'll get small shifts, which is slower since the magnitude of the shifts is far small in comparison.

The above illustrates why it's important to keep in mind that Boyer–Moore is very sensitive to character distribution, unlike the DFA-based algorithm (which we'll dive into later).

#### Good Suffix Rule

The good suffix rule is another pre-processing that occurs within the Boyer-Moore algorithm, which is slightly more complex than the above bad character rule:

The Boyer-Moore Wikipedia [article](https://en.wikipedia.org/wiki/Boyer%E2%80%93Moore_string-search_algorithm) gives a nice description:
> Suppose for a given alignment of _**P**_ and _**T**_, a substring _**t**_ of _**T**_ matches a suffix of _**P**_ and suppose _**t**_ is the largest such substring for the given alignment.
> 
> 1.  Then find, if it exists, the right-most copy _**t′**_ of _**t**_ in _**P**_ such that _**t′**_ is not a suffix of _**P**_ and the character to the left of _**t′**_ in _**P**_ differs from the character to the left of _**t**_ in _**P**_. Shift _**P**_ to the right so that substring _**t′**_ in _**P**_ aligns with substring _**t**_ in _**T**_.
> 2.  If _**t′**_ does not exist, then shift the left end of _**P**_ to the right by the least amount (past the left end of _**t**_ in _**T**_) so that a prefix of the shifted pattern matches a suffix of _**t**_ in _**T**_. This includes cases where _**t**_ is an exact match of _**P**_.
> 3.  If no such shift is possible, then shift _**P**_ by **m** (length of P) places to the right.

This library pre-computes the good-suffix rule using the `suffixLengths` and the `suffixShifts` functions (found in `Data.ByteString.Search.Internal.Utils` module).

Let's focus on the `suffixLengths` function first:

```idris
suffixLengths :  (bs : ByteString)
              -> {0 prf : So (not $ null bs)}
              -> F1 s (MArray s (length bs) Int)
suffixLengths bs t =
  let arr # t := marray1 (length bs) (the Int 0) t
    in case tryNatToFin (minus (length bs) 1) of
         Nothing  =>
           (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths: can't convert Nat to Fin") # t
         Just idx =>
           let () # t := set arr idx (cast {to=Int} (length bs)) t
               () # t := noSuffix (cast {to=Int} (minus (length bs) 2)) bs arr t
             in arr # t
  where
    dec :  (diff : Int)
        -> (j : Int)
        -> F1 s Int
    dec diff j t =
      case j < 0 of
        True  =>
          j # t
        False =>
          let j' := index (cast {to=Nat} j) bs
            in case j' of
                 Nothing  =>
                   (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.dec: can't index into ByteString") # t
                 Just j'' =>
                   let j''' := index (cast {to=Nat} (j + diff)) bs
                     in case j''' of
                          Nothing    =>
                            (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.dec: can't index into ByteString") # t
                          Just j'''' =>
                            case j'' /= j'''' of
                              True  =>
                                j # t
                              False =>
                                assert_total (dec diff (j - 1) t)
    mutual
      suffixLoop :  (pre : Int)
                 -> (end : Int)
                 -> (idx : Int)
                 -> (bs : ByteString)
                 -> (arr : MArray s (length bs) Int)
                 -> F1' s
      suffixLoop _   _   0   _  _   t =
        () # t
      suffixLoop pre end idx bs arr t =
        case pre < idx of
          True  =>
            let idx' := index (cast {to=Nat} idx) bs
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
                                  case tryNatToFin (cast {to=Nat} idx) of
                                    Nothing   =>
                                      (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.suffixLoop: can't convert Nat to Fin") # t
                                    Just idxs =>
                                      let () # t := set arr idxs 0 t
                                        in assert_total (suffixLoop pre (end - 1) (idx - 1) bs arr t)
                                False =>
                                  case tryNatToFin (cast {to=Nat} end) of
                                    Nothing   =>
                                      (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.suffixLoop: can't convert Nat to Fin") # t
                                    Just end' =>
                                      let prevs # t := get arr end' t
                                        in case tryNatToFin (cast {to=Nat} idx) of
                                             Nothing   =>
                                               (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.suffixLoop: can't convert Nat to Fin") # t
                                             Just idxs =>
                                               case (pre + prevs) < idx of
                                                 True  =>
                                                   let () # t := set arr idxs prevs t
                                                     in assert_total (suffixLoop pre (end - 1) (idx - 1) bs arr t)
                                                 False =>
                                                   let pri # t := dec (cast {to=Int} (minus (length bs) (cast {to=Nat} idx))) pre t
                                                       ()  # t := set arr idxs (idx - pri) t
                                                     in assert_total (suffixLoop pri (cast {to=Int} (minus (length bs) 2)) (idx - 1) bs arr t)
          False =>
            noSuffix idx bs arr t
      noSuffix :  (i : Int)
               -> (bs : ByteString)
               -> (arr : MArray s (length bs) Int)
               -> F1' s
      noSuffix 0 _  _   t =
        () # t
      noSuffix i bs arr t =
        let patati := index (cast {to=Nat} i) bs
          in case patati of
               Nothing      =>
                 (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.noSuffix: can't index into ByteString") # t
               Just patati' =>
                 let patatend := index (minus (length bs) 1) bs
                   in case patatend of
                        Nothing        =>
                          (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.noSuffix: can't index into ByteString") # t
                        Just patatend' => 
                          case patati' == patatend' of
                            True  =>
                              let diff      := (cast {to=Int} (minus (length bs) 1)) - i
                                  nexti     := i - 1
                                  previ # t := dec diff nexti t
                                in case tryNatToFin (cast {to=Nat} i) of
                                     Nothing =>
                                       (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.noSuffix: can't convert Nat to Fin") # t
                                     Just i' =>
                                       case previ == nexti of
                                         True  =>
                                           let () # t := set arr i' 1 t
                                             in assert_total (noSuffix nexti bs arr t)
                                         False =>
                                           let () # t := set arr i' (i - previ) t
                                             in assert_total (suffixLoop previ (cast {to=Int} (minus (length bs) 2)) nexti bs arr t)
                            False =>
                              case tryNatToFin (cast {to=Nat} i) of
                                Nothing =>
                                  (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixLengths.noSuffix: can't convert Nat to Fin") # t
                                Just i' =>
                                  let () # t := set arr i' 0 t
                                    in assert_total (noSuffix (i - 1) bs arr t)
```

`suffixLengths` helps determine the following:

For each position i in the pattern, `suffixLengths[i]` tells you how long a suffix of `P[0..i]` matches the suffix of the full pattern.

##### Example

Given the following pattern "ANPANMAN":

```
0 1 2 3 4 5 6 7
A N P A N M A N
```

The suffixes of the pattern are:

```
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

```
set arr[i] = i - previ
```

The above stores the number of characters backwards matched.

`suffixLoop` makes `suffixLengths` linear time instead of quadratic, it reuses previously computed suffix values if possible.

Now, we can dive into the `suffixShifts` function:

```idris
suffixShifts :  (bs : ByteString)
             -> {0 prf : So (not $ null bs)}
             -> F1 s (MArray s (length bs) Int)
suffixShifts bs {prf} t =
  let arr  # t := marray1 (length bs) (cast {to=Int} (length bs)) t
      suff # t := suffixLengths bs {prf=prf} t
      ()   # t := prefixShift (cast {to=Int} (minus (length bs) 2)) 0 bs suff arr t
      ()   # t := suffixShift 0 bs suff arr t
    in arr # t
  where
    fillToShift :  (i : Int)
                -> (shift : Int)
                -> (bs : ByteString)
                -> (arr : MArray s (length bs) Int)
                -> F1' s
    fillToShift i shift bs arr t =
      case i == shift of
        True =>
          () # t
        False =>
          case tryNatToFin (cast {to=Nat} i) of
            Nothing =>
              (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixShifts.fillToShift: can't convert Nat to Fin") # t
            Just i' =>
              let () # t := set arr i' shift t
                in assert_total (fillToShift (i + 1) shift bs arr t)
    prefixShift :  (idx : Int)
                -> (j : Int)
                -> (bs : ByteString)
                -> (suff : MArray s (length bs) Int)
                -> (arr : MArray s (length bs) Int)
                -> F1' s
    prefixShift idx j bs suff arr t =
      case idx < 0 of
        True  =>
          () # t
        False =>
          case tryNatToFin (cast {to=Nat} idx) of
            Nothing   =>
              (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixShifts.prefixShift: can't convert Nat to Fin") # t
            Just idx' =>
              let idx'' # t := get suff idx' t
                in case idx'' == (idx + 1) of
                     True =>
                       let shift  := (cast {to=Int} (minus (length bs) 1)) - idx
                           () # t := fillToShift j shift bs arr t
                         in assert_total (prefixShift (idx - 1) shift bs suff arr t)                                      
                     False =>
                       assert_total (prefixShift (idx - 1) j bs suff arr t)
    suffixShift :  (idx : Int)
                -> (bs : ByteString)
                -> (suff : MArray s (length bs) Int)
                -> (arr : MArray s (length bs) Int)
                -> F1' s
    suffixShift idx bs suff arr t =
      let patend := cast {to=Int} (minus (length bs) 1)
        in case idx >= patend of
             True  =>
               () # t
             False =>
               case tryNatToFin (cast {to=Nat} idx) of
                 Nothing   =>
                   (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixShifts.suffixShift: can't convert Nat to Fin") # t
                 Just idx' =>
                   let idx'' # t := get suff idx' t
                       target    := patend - idx''
                     in case tryNatToFin (cast {to=Nat} target) of
                          Nothing      =>
                            (assert_total $ idris_crash "Data.ByteString.Search.Internal.Utils.suffixShifts.suffixShift: can't convert Nat to Fin") # t
                          Just target' =>
                            let value  := patend - idx
                                () # t := set arr target' value t
                              in assert_total (suffixShift (idx + 1) bs suff arr t)
```

`suffixShifts` uses the lengths from `suffixLengths` to compute the actual suffix shifts.

`prefixShifts` shifts the pattern so that prefix lines up with the suffix if a suffix of the matched portion is also a prefix of the pattern.

`suffixShift` shifts the pattern so that the next instance of that suffix aligns if a mismatch occurred at index `i` and the suffix length is `s`, which looks like `shift = (pattern length - 1) - i`.

##### Example

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

Given a pattern `P` of length `m` (length of `P`) and an alphabet `Σ` (Bytes = 256 values), the goal is to build a DFA using the `automaton` function found in the `Data.ByteString.Search.Internal.Utils` module:

```idris
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
```
The automaton is:

> A table `δ(state, byte) → nextState`

Where:

-   `state` = how many characters of the pattern we have matched so far (`0 … m`)
    
-   `byte` = next input character (`0 … 255`)
    
-   `nextState` = the new amount of the pattern matched after seeing that byte

Early on in the `automaton` function, we create an `MArray` of `(m + 1) states * 256 bytes` size:

```
MArray s (mult (plus (length bs) 1) 256) Nat
```

Which flattens `(state, byte)` into a single array.

The `go` and `fillState` nested functions build the DFA row by row, and then the `loop` nested function loops over every byte value from 0 -> 255.

Keep in mind, the KMP borders are already pre-computed via the `kmpBorders` function (more on this later). The array generated by `kmpBorders` encodes all valid fallback transitions, avoiding expensive back-tracking upon mismatches.

#### Example

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
```

What's unique about `kmpBorders` is that it actually computes the _suffix_-oriented table, instead of the typical prefix-oriented table.
This is certainly preferred since that allows for a more natural implementation via structural recursion.
The table helps efficiently skip positions in the pattern during sub-string search, while descending from longer prefixes to shorter ones.

#### Example

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

```
m <-> length of pattern being searched for
n <-> length of text being searched across
k <-> |Σ| is the size of the alphabet
```
