module BoyerMoore.Internal

import Data.ByteString
import Data.ByteString.Search.BoyerMoore.Internal
import Data.Enum
import Data.Linear.Ref1
import Data.Linear.Token
import Hedgehog

%default total

||| Verify that a Boyer–Moore integer table entry can be written and read
||| using the bounded `PatternIndex` representation.
|||
prop_bmIntTable_4_7 : Property
prop_bmIntTable_4_7 =
  property1 $ do
    ( run1 $ \t =>
        let table # t :=
              newBMIntTable {size = 8} t

            idx : PatternIndex 8
            idx = 4

            _ # t :=
              bmSet
                table
                idx
                7
                t

            result # t :=
              bmGet
                table
                idx
                t

         in result # t ) === the Int 7

||| Verify that an occurrence-table entry can be written and read directly
||| using a `Bits8` index.
|||
prop_occurrence_A : Property
prop_occurrence_A =
  property1 $ do
    ( run1 $ \t =>
        let table # t :=
              newOccurrenceTable t

            _ # t :=
              setOccurrence
                table
                65
                (-6)
                t

            result # t :=
              occurrence
                table
                65
                t

         in result # t ) === the Int (-6)

||| Verify the bad-character occurrence table generated for `"ANPANMAN"`.
|||
||| The final pattern byte is excluded from preprocessing.
|||
||| Expected non-default entries:
|||
||| | byte | char | value |
||| | ---- | ---- | ----- |
||| | 65   | A    | -6    |
||| | 77   | M    | -5    |
||| | 78   | N    | -4    |
||| | 80   | P    | -2    |
|||
prop_occurrences_ANPANMAN : Property
prop_occurrences_ANPANMAN =
  property1 $ do
    ( run1 $ \t =>
        let pat :=
              Prelude.unpack "ANPANMAN"

            patbs :=
              Data.ByteString.pack
                (map (cast {to=Bits8}) pat)

            table' # t :=
              occurrences patbs {prf = believe_me ()} t

         in case table' of
              Nothing =>
                (the (List Int) []) # t

              Just table =>
                let a # t := occurrence table 65 t
                    m # t := occurrence table 77 t
                    n # t := occurrence table 78 t
                    p # t := occurrence table 80 t
                    x # t := occurrence table 88 t

                 in [a, m, n, p, x] # t ) === [ -6
                                              , -5
                                              , -4
                                              , -2
                                              , 1
                                              ]

||| Verify the bad-character occurrence table generated for `"ABCABC"`.
|||
||| The final `C` is excluded, so the last relevant positions are:
|||
||| A -> index 3 -> -3
||| B -> index 4 -> -4
||| C -> index 2 -> -2
|||
prop_occurrences_ABCABC : Property
prop_occurrences_ABCABC =
  property1 $ do
    ( run1 $ \t =>
        let pat :=
              Prelude.unpack "ABCABC"

            patbs :=
              Data.ByteString.pack
                (map (cast {to=Bits8}) pat)

            table' # t :=
              occurrences patbs {prf = believe_me ()} t

         in case table' of
              Nothing =>
                (the (List Int) []) # t

              Just table =>
                let a # t := occurrence table 65 t
                    b # t := occurrence table 66 t
                    c # t := occurrence table 67 t
                    x # t := occurrence table 88 t

                 in [a, b, c, x] # t ) === [ -3
                                           , -4
                                           , -2
                                           , 1
                                           ]

||| Verify the suffix-length table generated for `"ANPANMAN"`.
|||
||| Expected suffix lengths:
|||
||| [0, 2, 0, 0, 2, 0, 0, 8]
|||
prop_suffixLengths_ANPANMAN : Property
prop_suffixLengths_ANPANMAN =
  property1 $ do
    ( run1 $ \t =>
        let pat :=
              Prelude.unpack "ANPANMAN"

            patbs :=
              Data.ByteString.pack
                (map (cast {to=Bits8}) pat)

            table' # t :=
              suffixLengths patbs {prf = believe_me ()} t

         in case table' of
              Nothing =>
                (the (List Int) []) # t

              Just (MkBMPatternTable stspace table) =>
                let Just i0 := toPatternIndex stspace 0
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i1 := toPatternIndex stspace 1
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i2 := toPatternIndex stspace 2
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i3 := toPatternIndex stspace 3
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i4 := toPatternIndex stspace 4
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i5 := toPatternIndex stspace 5
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i6 := toPatternIndex stspace 6
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i7 := toPatternIndex stspace 7
                      | Nothing =>
                          (the (List Int) []) # t

                    r0 # t := bmGet table i0 t
                    r1 # t := bmGet table i1 t
                    r2 # t := bmGet table i2 t
                    r3 # t := bmGet table i3 t
                    r4 # t := bmGet table i4 t
                    r5 # t := bmGet table i5 t
                    r6 # t := bmGet table i6 t
                    r7 # t := bmGet table i7 t

                 in [r0, r1, r2, r3, r4, r5, r6, r7] # t ) === [ 0
                                                               , 2
                                                               , 0
                                                               , 0
                                                               , 2
                                                               , 0
                                                               , 0
                                                               , 8
                                                               ]

||| Verify the suffix-length table generated for `"ABCABC"`.
|||
||| Expected suffix lengths:
|||
||| [0, 0, 3, 0, 0, 6]
|||
prop_suffixLengths_ABCABC : Property
prop_suffixLengths_ABCABC =
  property1 $ do
    ( run1 $ \t =>
        let pat :=
              Prelude.unpack "ABCABC"

            patbs :=
              Data.ByteString.pack
                (map (cast {to=Bits8}) pat)

            table' # t :=
              suffixLengths patbs {prf = believe_me ()} t

         in case table' of
              Nothing =>
                (the (List Int) []) # t

              Just (MkBMPatternTable stspace table) =>
                let Just i0 := toPatternIndex stspace 0
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i1 := toPatternIndex stspace 1
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i2 := toPatternIndex stspace 2
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i3 := toPatternIndex stspace 3
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i4 := toPatternIndex stspace 4
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i5 := toPatternIndex stspace 5
                      | Nothing =>
                          (the (List Int) []) # t

                    r0 # t := bmGet table i0 t
                    r1 # t := bmGet table i1 t
                    r2 # t := bmGet table i2 t
                    r3 # t := bmGet table i3 t
                    r4 # t := bmGet table i4 t
                    r5 # t := bmGet table i5 t

                 in [r0, r1, r2, r3, r4, r5] # t ) === [ 0
                                                       , 0
                                                       , 3
                                                       , 0
                                                       , 0
                                                       , 6
                                                       ]

||| Verify the good-suffix shift table generated for `"ANPANMAN"`.
|||
||| Expected suffix shifts:
|||
||| [6, 6, 6, 6, 6, 3, 8, 1]
|||
prop_suffixShifts_ANPANMAN : Property
prop_suffixShifts_ANPANMAN =
  property1 $ do
    ( run1 $ \t =>
        let pat :=
              Prelude.unpack "ANPANMAN"

            patbs :=
              Data.ByteString.pack
                (map (cast {to=Bits8}) pat)

            table' # t :=
              suffixShifts patbs {prf = believe_me ()} t

         in case table' of
              Nothing =>
                (the (List Int) []) # t

              Just (MkBMPatternTable stspace table) =>
                let Just i0 := toPatternIndex stspace 0
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i1 := toPatternIndex stspace 1
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i2 := toPatternIndex stspace 2
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i3 := toPatternIndex stspace 3
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i4 := toPatternIndex stspace 4
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i5 := toPatternIndex stspace 5
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i6 := toPatternIndex stspace 6
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i7 := toPatternIndex stspace 7
                      | Nothing =>
                          (the (List Int) []) # t

                    r0 # t := bmGet table i0 t
                    r1 # t := bmGet table i1 t
                    r2 # t := bmGet table i2 t
                    r3 # t := bmGet table i3 t
                    r4 # t := bmGet table i4 t
                    r5 # t := bmGet table i5 t
                    r6 # t := bmGet table i6 t
                    r7 # t := bmGet table i7 t

                 in [r0, r1, r2, r3, r4, r5, r6, r7] # t ) === [ 6
                                                               , 6
                                                               , 6
                                                               , 6
                                                               , 6
                                                               , 3
                                                               , 8
                                                               , 1
                                                               ]

||| Verify the good-suffix shift table generated for `"ABCABC"`.
|||
||| Expected suffix shifts:
|||
||| [3, 3, 3, 6, 6, 1]
|||
prop_suffixShifts_ABCABC : Property
prop_suffixShifts_ABCABC =
  property1 $ do
    ( run1 $ \t =>
        let pat :=
              Prelude.unpack "ABCABC"

            patbs :=
              Data.ByteString.pack
                (map (cast {to=Bits8}) pat)

            table' # t :=
              suffixShifts patbs {prf = believe_me ()} t

         in case table' of
              Nothing =>
                (the (List Int) []) # t

              Just (MkBMPatternTable stspace table) =>
                let Just i0 := toPatternIndex stspace 0
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i1 := toPatternIndex stspace 1
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i2 := toPatternIndex stspace 2
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i3 := toPatternIndex stspace 3
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i4 := toPatternIndex stspace 4
                      | Nothing =>
                          (the (List Int) []) # t

                    Just i5 := toPatternIndex stspace 5
                      | Nothing =>
                          (the (List Int) []) # t

                    r0 # t := bmGet table i0 t
                    r1 # t := bmGet table i1 t
                    r2 # t := bmGet table i2 t
                    r3 # t := bmGet table i3 t
                    r4 # t := bmGet table i4 t
                    r5 # t := bmGet table i5 t

                 in [r0, r1, r2, r3, r4, r5] # t ) === [ 3
                                                       , 3
                                                       , 3
                                                       , 6
                                                       , 6
                                                       , 1
                                                       ]

export
props : Group
props =
  MkGroup "BoyerMoore.Internal"
    [ ("prop_bmIntTable_4_7", prop_bmIntTable_4_7)
    , ("prop_occurrence_A", prop_occurrence_A)
    , ("prop_occurrences_ANPANMAN", prop_occurrences_ANPANMAN)
    , ("prop_occurrences_ABCABC", prop_occurrences_ABCABC)
    , ("prop_suffixLengths_ANPANMAN", prop_suffixLengths_ANPANMAN)
    , ("prop_suffixLengths_ABCABC", prop_suffixLengths_ABCABC)
    , ("prop_suffixShifts_ANPANMAN", prop_suffixShifts_ANPANMAN)
    , ("prop_suffixShifts_ABCABC", prop_suffixShifts_ABCABC)
    ]
