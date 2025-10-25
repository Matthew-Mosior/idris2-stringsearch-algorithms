module Utils

import Hedgehog
import Data.Array
import Data.ByteString
import Data.ByteString.Search.Internal.Utils
import Data.Fin
import Data.Linear.Ref1
import Data.Linear.Token
import Data.Vect

||| prop_kmpBorders: "ANPANMAN"
|||  
||| | Index | Value | Explanation       |
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
||| | Flat index | Value | Meaning (decoded) |
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
                                                                                                
export
props : Group
props = MkGroup "Utils"
  [ ("prop_kmpBorders", prop_kmpBorders)
  , ("prop_automaton", prop_automaton)
  ]
