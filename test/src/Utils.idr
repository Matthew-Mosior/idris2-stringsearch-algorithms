module Utils

import Data.ByteString.Search.Internal.Utils

import Hedgehog
import Data.Array
import Data.ByteString
import Data.Fin
import Data.Linear.Ref1
import Data.Linear.Token
import Data.So
import Data.Vect

||| prop_kmpBorders: "ANPANMAN"
|||  
||| | index | value | explanation       |
||| | ----- | ----- | ----------------- |
||| | 0     | 0     | border(0) = 0     |
||| | 1     | 0     | "A" → no border   |
||| | 2     | 0     | "AN" → no border  |
||| | 3     | 0     | "ANP" → no border |
||| | 4     | 1     | "ANPA" → "A"      |
||| | 5     | 2     | "ANPAN" → "AN"    |
||| | 6     | 0     | "ANPANM" → none   |
||| | 7     | 1     | "ANPANMA" → "A"   |
||| | 8     | 2     | "ANPANMAN" → "AN" |
|||
prop_kmpBorders : Property
prop_kmpBorders = property1 $
  ( run1 $ \t =>
      let pat             := Prelude.unpack "ANPANMAN"
          patbs           := Data.ByteString.pack (map (cast {to=Bits8}) pat)
          kmpborders  # t := kmpBorders patbs t
          kmpborders' # t := Data.Array.Core.freeze kmpborders t
        in Prelude.Interfaces.toList kmpborders' # t ) === [0,0,0,0,1,2,0,1,2]

||| prop_kmpBorders': "ABCABC"
|||  
||| | index | value | explanation       |
||| | ----- | ----- | ----------------- |
||| | 0     | 0     | border(0) = 0     |
||| | 1     | 0     | "A" → no border   |
||| | 2     | 0     | "AB" → no border  |
||| | 3     | 0     | "ABC" → no border |
||| | 4     | 1     | "ABCA" → "A"      |
||| | 5     | 2     | "ABCAB" → "AB"    |
||| | 6     | 3     | "ABCABC" → "ABC"  |
|||
prop_kmpBorders' : Property
prop_kmpBorders' = property1 $
  ( run1 $ \t =>
      let pat             := Prelude.unpack "ABCABC"
          patbs           := Data.ByteString.pack (map (cast {to=Bits8}) pat)
          kmpborders  # t := kmpBorders patbs t
          kmpborders' # t := Data.Array.Core.freeze kmpborders t
        in Prelude.Interfaces.toList kmpborders' # t ) === [0,0,0,0,1,2,3]

||| prop_automaton : "ANPANMAN"
|||
||| | flat index | value | meaning (decoded) |
||| | ---------- | ----- | ----------------- |
||| | 65         | 1     | δ(0, 'A') = 1     |
||| | 321        | 1     | δ(1, 'A') = 1     |
||| | 334        | 2     | δ(1, 'N') = 2     |
||| | 577        | 1     | δ(2, 'A') = 1     |
||| | 592        | 3     | δ(2, 'P') = 3     |
||| | 833        | 4     | δ(3, 'A') = 4     |
||| | 1089       | 1     | δ(4, 'A') = 1     |
||| | 1102       | 5     | δ(4, 'N') = 5     |
||| | 1345       | 1     | δ(5, 'A') = 1     |
||| | 1357       | 6     | δ(5, 'M') = 6     |
||| | 1601       | 7     | δ(6, 'A') = 7     |
||| | 1857       | 1     | δ(7, 'A') = 1     |
||| | 1870       | 8     | δ(7, 'N') = 8     |
||| | 2113       | 1     | δ(8, 'A') = 1     |
|||
prop_automaton : Property
prop_automaton = property1 $
  ( run1 $ \t =>
      let pat             := Prelude.unpack "ANPANMAN"
          patbs           := Data.ByteString.pack (map (cast {to=Bits8}) pat)
          automaton'  # t := automaton patbs t
          automaton'' # t := Data.Array.Core.freeze automaton' t
          vect            := toVectWithIndex automaton''
          list            := Prelude.Interfaces.toList vect
        in filter (\(_, b) => b /= (the Nat 0)) (map (\(a, b) => (finToNat a, b)) list) # t) === [ (65, 1)
                                                                                                 , (321, 1)
                                                                                                 , (334, 2)
                                                                                                 , (577, 1)
                                                                                                 , (592, 3)
                                                                                                 , (833, 4)
                                                                                                 , (1089, 1)
                                                                                                 , (1102, 5)
                                                                                                 , (1345, 1)
                                                                                                 , (1357, 6)
                                                                                                 , (1601, 7)
                                                                                                 , (1857, 1)
                                                                                                 , (1870, 8)
                                                                                                 , (2113, 1)
                                                                                                 ]                  

||| prop_automaton' : "ABCABC"
|||
||| | flat index | value | meaning      |
||| | ---------- | ----- | ------------ |
||| |         65 |     1 | δ(0,'A') = 1 |
||| |        321 |     1 | δ(1,'A') = 1 |
||| |        322 |     2 | δ(1,'B') = 2 |
||| |        577 |     1 | δ(2,'A') = 1 |
||| |        579 |     3 | δ(2,'C') = 3 |
||| |        833 |     4 | δ(3,'A') = 4 |
||| |       1089 |     1 | δ(4,'A') = 1 |
||| |       1090 |     5 | δ(4,'B') = 5 |
||| |       1345 |     1 | δ(5,'A') = 1 |
||| |       1347 |     6 | δ(5,'C') = 6 |
||| |       1601 |     1 | δ(6,'A') = 1 |
|||
prop_automaton' : Property
prop_automaton' = property1 $
  ( run1 $ \t =>
      let pat             := Prelude.unpack "ABCABC"
          patbs           := Data.ByteString.pack (map (cast {to=Bits8}) pat)
          automaton'  # t := automaton patbs t
          automaton'' # t := Data.Array.Core.freeze automaton' t
          vect            := toVectWithIndex automaton''
          list            := Prelude.Interfaces.toList vect
        in filter (\(_, b) => b /= (the Nat 0)) (map (\(a, b) => (finToNat a, b)) list) # t) === [ (65, 1)
                                                                                                 , (321, 1)
                                                                                                 , (322, 2)
                                                                                                 , (577, 1)
                                                                                                 , (579, 3)
                                                                                                 , (833, 4)
                                                                                                 , (1089, 1)
                                                                                                 , (1090, 5)
                                                                                                 , (1345, 1)
                                                                                                 , (1347, 6)
                                                                                                 , (1601, 1)
                                                                                                 ]
               

||| prop_occurrences: "ANPANMAN"
|||
||| | flat index / ASCII | char | value |
||| | ------------------ | ---- | ----- |
||| |        65          | 'A'  |    -6 |
||| |        77          | 'M'  |    -5 |
||| |        78          | 'N'  |    -4 |
||| |        80          | 'P'  |    -2 |
|||
prop_occurrences : Property
prop_occurrences = property1 $
  let pat   := Prelude.unpack "ANPANMAN"
      patbs := Data.ByteString.pack (map (cast {to=Bits8}) pat)
    in case decSo $ (not $ null patbs) of
         No  _          =>
           assert_total $ idris_crash "pat is null"
         Yes notnullprf =>
           ( run1 $ \t =>
               let occurrences'  # t := occurrences patbs {prf=notnullprf} t
                   occurrences'' # t := Data.Array.Core.freeze occurrences' t
                   vect              := toVectWithIndex occurrences''
                   list              := Prelude.Interfaces.toList vect
                 in filter (\(_, b) => b /= (the Int 1)) (map (\(a, b) => (finToNat a, b)) list) # t) === [ (65, -6)
                                                                                                          , (77, -5)
                                                                                                          , (78, -4)
                                                                                                          , (80, -2)
                                                                                                          ]

||| prop_occurrences': "ABCABC"
|||
|||| flat index / ASCII | char | value |
|||| ------------------ | ---- | ----- |
||||        65          | 'A'  | -3    |
||||        66          | 'B'  | -4    |
||||        67          | 'C'  | -2    |
|||
prop_occurrences' : Property
prop_occurrences' = property1 $
  let pat   := Prelude.unpack "ABCABC"
      patbs := Data.ByteString.pack (map (cast {to=Bits8}) pat)
    in case decSo $ (not $ null patbs) of
         No  _          =>
           assert_total $ idris_crash "pat is null"
         Yes notnullprf =>
           ( run1 $ \t =>
               let occurrences'  # t := occurrences patbs {prf=notnullprf} t
                   occurrences'' # t := Data.Array.Core.freeze occurrences' t
                   vect              := toVectWithIndex occurrences''
                   list              := Prelude.Interfaces.toList vect
                 in filter (\(_, b) => b /= (the Int 1)) (map (\(a, b) => (finToNat a, b)) list) # t) === [ (65, -3)
                                                                                                          , (66, -4)
                                                                                                          , (67, -2)
                                                                                                          ]

||| prop_suffixLengths: "ANPANMAN"
|||
||| Raw suffix-lengths array used to compute the good suffix shift table
|||
||| | i | pat[i] | matches pattern end? | diff = patEnd - i | nextI = i-1 | prevI (dec diff nextI) | ar[i] |
||| | - | ------ | -------------------- | ----------------- | ----------- | ---------------------- | ----- |
||| | 0 |    A   |          No          |         -         |      -      |            -           |   0   |
||| | 1 |    N   |          Yes         |         6         |      0      |           -1           |   2   |
||| | 2 |    P   |          No          |         -         |      -      |            -           |   0   |
||| | 3 |    A   |          No          |         -         |      -      |            -           |   0   |
||| | 4 |    N   |          Yes         |         3         |      3      |            2           |   2   |
||| | 5 |    M   |          No          |         -         |      -      |            -           |   0   |
||| | 6 |    A   |          No          |         -         |      -      |            -           |   0   |
||| | 7 |    N   |       - (last)       |         -         |      -      |            -           |   8   |
|||
prop_suffixLengths : Property
prop_suffixLengths = property1 $
  let pat   := Prelude.unpack "ANPANMAN"
      patbs := Data.ByteString.pack (map (cast {to=Bits8}) pat)
    in case decSo $ (not $ null patbs) of
         No  _          =>
           assert_total $ idris_crash "pat is null"
         Yes notnullprf =>
           ( run1 $ \t =>
               let suffixlengths  # t := suffixLengths patbs {prf=notnullprf} t
                   suffixlengths' # t := Data.Array.Core.freeze suffixlengths t
                 in Prelude.Interfaces.toList suffixlengths' # t ) === [0,2,0,0,2,0,0,8]

||| prop_suffixLengths': "ABCABC"
|||
||| Raw suffix-lengths array used to compute the good suffix shift table
|||
||| | i | pat[i] | matches pattern end? (pat[i] == pe) | diff = patEnd - i | nextI = i-1 | prevI (dec diff nextI) | ar[i] |
||| | - | ------ | ----------------------------------- | ----------------- | ----------- | ---------------------- | ----- |
||| | 0 |    A   |                  No                 |         -         |      -      |            -           |   0   |
||| | 1 |    B   |                  No                 |         -         |      -      |            -           |   0   |
||| | 2 |    C   |                 Yes                 |         3         |      1      |           -1           |   3   |
||| | 3 |    A   |                  No                 |         -         |      -      |            -           |   0   |
||| | 4 |    B   |                  No                 |         -         |      -      |            -           |   0   |
||| | 5 |    C   |               - (last)              |         -         |      -      |            -           |   6   |
|||
prop_suffixLengths' : Property
prop_suffixLengths' = property1 $
  let pat   := Prelude.unpack "ABCABC"
      patbs := Data.ByteString.pack (map (cast {to=Bits8}) pat)
    in case decSo $ (not $ null patbs) of
         No  _          =>
           assert_total $ idris_crash "pat is null"
         Yes notnullprf =>
           ( run1 $ \t =>
               let suffixlengths  # t := suffixLengths patbs {prf=notnullprf} t
                   suffixlengths' # t := Data.Array.Core.freeze suffixlengths t
                 in Prelude.Interfaces.toList suffixlengths' # t ) === [0,0,3,0,0,6]

||| prop_suffixShifts: "ANPANMAN"
||| | idx | suff[idx] | target = patEnd - suff[idx] | value = patEnd - idx |    ar after write |
||| | --- | --------- | --------------------------- | -------------------- | ----------------- |
||| |   0 |         0 |                   7 - 0 = 7 |            7 - 0 = 7 | [6,6,6,6,6,6,8,7] |
||| |   1 |         2 |                   7 - 2 = 5 |            7 - 1 = 6 | [6,6,6,6,6,6,8,7] |
||| |   2 |         0 |                           7 |            7 - 2 = 5 | [6,6,6,6,6,6,8,5] |
||| |   3 |         0 |                           7 |            7 - 3 = 4 | [6,6,6,6,6,6,8,4] |
||| |   4 |         2 |                   7 - 2 = 5 |            7 - 4 = 3 | [6,6,6,6,6,3,8,4] |
||| |   5 |         0 |                           7 |            7 - 5 = 2 | [6,6,6,6,6,3,8,2] |
||| |   6 |         0 |                           7 |            7 - 6 = 1 | [6,6,6,6,6,3,8,1] |
|||
prop_suffixShifts : Property
prop_suffixShifts = property1 $
  let pat   := Prelude.unpack "ANPANMAN"
      patbs := Data.ByteString.pack (map (cast {to=Bits8}) pat)
    in case decSo $ (not $ null patbs) of
         No  _          =>
           assert_total $ idris_crash "pat is null"
         Yes notnullprf =>
           ( run1 $ \t =>
               let suffixshifts  # t := suffixShifts patbs {prf=notnullprf} t
                   suffixshifts' # t := Data.Array.Core.freeze suffixshifts t
                 in Prelude.Interfaces.toList suffixshifts' # t ) === [6,6,6,6,6,3,8,1]

||| prop_suffixShifts': "ABCABC"
|||
||| | idx | suff[idx] | target = patEnd - suff[idx] | value = patEnd - idx | ar after write |
||| | --- | --------- | --------------------------- | -------------------- | -------------- |
||| |   0 |         0 |                   5 - 0 = 5 |            5 - 0 = 5 |  [3,3,3,6,6,5] |
||| |   1 |         0 |                           5 |            5 - 1 = 4 |  [3,3,3,6,6,4] |
||| |   2 |         3 |                   5 - 3 = 2 |            5 - 2 = 3 |  [3,3,3,6,6,4] |
||| |   3 |         0 |                           5 |            5 - 3 = 2 |  [3,3,3,6,6,2] |
||| |   4 |         0 |                           5 |            5 - 4 = 1 |  [3,3,3,6,6,1] |
|||
prop_suffixShifts' : Property
prop_suffixShifts' = property1 $
  let pat   := Prelude.unpack "ABCABC"
      patbs := Data.ByteString.pack (map (cast {to=Bits8}) pat)
    in case decSo $ (not $ null patbs) of
         No  _          =>
           assert_total $ idris_crash "pat is null"
         Yes notnullprf =>
           ( run1 $ \t =>
               let suffixshifts  # t := suffixShifts patbs {prf=notnullprf} t
                   suffixshifts' # t := Data.Array.Core.freeze suffixshifts t
                 in Prelude.Interfaces.toList suffixshifts' # t ) === [3,3,3,6,6,1]

export
props_ANPANMAN : Group
props_ANPANMAN = MkGroup "Utils: ANPANMAN"
  [ ("prop_kmpBorders", prop_kmpBorders)
  , ("prop_automaton", prop_automaton)
  , ("prop_occurrences", prop_occurrences)
  , ("prop_suffixLengths", prop_suffixLengths)
  , ("prop_suffixShifts", prop_suffixShifts)
  ]

export
props_ABCABC : Group
props_ABCABC = MkGroup "Utils: ABCABC"
  [ ("prop_kmpBorders'", prop_kmpBorders')
  , ("prop_automaton'", prop_automaton')
  , ("prop_occurrences'", prop_occurrences')
  , ("prop_suffixLengths'", prop_suffixLengths')
  , ("prop_suffixShifts'", prop_suffixShifts')
  ]
