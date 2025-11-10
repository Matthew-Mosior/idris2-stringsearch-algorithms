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
           assert_total $ idris_crash "awef"
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

||| prop_suffixLengths: "ANPANMAN"
|||
||| Raw suffix-lengths array used to compute the good suffix shift table
|||
||| | i | pat[i] | matches pattern end? | diff | nextI | prevI | ar[i] |
||| | - | ------ | -------------------- | ---- | ----- | ----- | ----- |
||| | 0 | A      | No                   | -    | -     | -     | 0     |
||| | 1 | N      | Yes                  | 6    | 0     | 0     | 1     |
||| | 2 | P      | No                   | -    | -     | -     | 0     |
||| | 3 | A      | No                   | -    | -     | -     | 0     |
||| | 4 | N      | Yes                  | 3    | 3     | 3     | 1     |
||| | 5 | M      | No                   | -    | -     | -     | 0     |
||| | 6 | A      | No                   | -    | -     | -     | 0     |
||| | 7 | N      | -                    | -    | -     | -     | 8     |
|||
prop_suffixLengths : Property
prop_suffixLengths = property1 $
  let pat   := Prelude.unpack "ANPANMAN"
      patbs := Data.ByteString.pack (map (cast {to=Bits8}) pat)
    in case decSo $ (not $ null patbs) of
         No  _          =>
           assert_total $ idris_crash "awef"
         Yes notnullprf =>
           ( run1 $ \t =>
               let suffixlengths  # t := suffixLengths patbs {prf=notnullprf} t
                   suffixlengths' # t := Data.Array.Core.freeze suffixlengths t
                 in Prelude.Interfaces.toList suffixlengths' # t ) === [0,1,0,0,1,0,0,8]

||| prop_suffixShifts: "ANPANMAN"
|||
|||| | idx | suff[idx] | target = 7 - suff[idx] | value = 7 - idx | array after write | What's changing            |
|||| | --- | --------- | ---------------------- | --------------- | ----------------- | -------------------------- |
|||| | 0   | 1         | 6                      | 7               | [8,8,8,8,8,8,7,8] | arr[6] updated             |
|||| | 1   | 1         | 6                      | 6               | [8,8,8,8,8,8,6,8] | arr[6] overwritten         |
|||| | 2   | 1         | 6                      | 5               | [8,8,8,8,8,8,5,8] | arr[6] overwritten         |
|||| | 3   | 1         | 6                      | 4               | [8,8,8,8,8,8,4,8] | arr[6] overwritten         |
|||| | 4   | 1         | 6                      | 3               | [8,8,8,8,8,8,3,8] | arr[6] overwritten         |
|||| | 5   | 1         | 6                      | 2               | [8,8,8,8,8,8,2,8] | arr[6] overwritten         |
|||| | 6   | 3         | 4                      | 1               | [8,8,8,8,8,8,3,1] | arr[4] updated, arr[7] = 1 |
|||
prop_suffixShifts : Property
prop_suffixShifts = property1 $
  let pat   := Prelude.unpack "ANPANMAN"
      patbs := Data.ByteString.pack (map (cast {to=Bits8}) pat)
    in case decSo $ (not $ null patbs) of
         No  _          =>
           assert_total $ idris_crash "awef"
         Yes notnullprf =>
           ( run1 $ \t =>
               let suffixshifts  # t := suffixShifts patbs {prf=notnullprf} t
                   suffixshifts' # t := Data.Array.Core.freeze suffixshifts t
                 in Prelude.Interfaces.toList suffixshifts' # t ) === [8,8,8,8,8,8,3,1]

export
props : Group
props = MkGroup "Utils"
  [ ("prop_kmpBorders", prop_kmpBorders)
  , ("prop_automaton", prop_automaton)
  , ("prop_occurrences", prop_occurrences)
  , ("prop_suffixLengths", prop_suffixLengths)
  , ("prop_suffixShifts", prop_suffixShifts)
  ]
