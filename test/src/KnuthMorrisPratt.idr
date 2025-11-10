module KnuthMorrisPratt

import Data.ByteString.Search.Internal.Utils
import Data.ByteString.Search.KnuthMorrisPratt

import Hedgehog
import Data.Array
import Data.ByteString
import Data.Fin
import Data.Linear.Ref1
import Data.Linear.Token
import Data.So
import Data.Vect

||| prop_matcher:
|||
||| pat:    "AN"
||| target: "ANPANMAN"
|||
||| | Start | Substring   |
||| | ----- | ----------- |
||| | 0     | "AN"PANMAN  |
||| | 3     | "AN"P ANMAN |
||| | 6     | "AN"        |
|||
prop_matcher : Property
prop_matcher = property1 $
  ( run1 $ \t =>
      let pat             := Prelude.unpack "AN"
          target          := Prelude.unpack "ANPANMAN"
          patbs           := Data.ByteString.pack (map (cast {to=Bits8}) pat)
          targetbs        := Data.ByteString.pack (map (cast {to=Bits8}) target)
        in matcher False patbs [targetbs] t) === [0,3,6]

{-
||| prop_matchKMP:
|||
||| pat:    "AN"
||| target: "ANPANMAN"
|||
||| target | A | N | P | A | N | M | A | N
||| index  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7
||| match  | Y | N | N | Y | N | N | Y | N
|||
prop_matchKMP : Property
prop_matchKMP = property1 $
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
-}

export
props : Group
props = MkGroup "KnuthMorrisPratt"
  [ ("prop_matcher", prop_matcher)
--  , ("prop_matchKMP", prop_matchKMP)
  ]
