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

||| prop_false_matcher:
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
||| matcher False "AN" ["ANPANMAN"] => [0, 3, 6]
|||
prop_false_matcher : Property
prop_false_matcher = property1 $
  ( run1 $ \t =>
      let pat             := Prelude.unpack "AN"
          target          := Prelude.unpack "ANPANMAN"
          patbs           := Data.ByteString.pack (map (cast {to=Bits8}) pat)
          targetbs        := Data.ByteString.pack (map (cast {to=Bits8}) target)
        in matcher False patbs [targetbs] t) === [0,3,6]

||| prop_true_matcher:
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
||| matcher True "AN" ["ANPANMAN"] => [0, 3, 6]
|||
prop_true_matcher : Property
prop_true_matcher = property1 $
  ( run1 $ \t =>
      let pat             := Prelude.unpack "AN"
          target          := Prelude.unpack "ANPANMAN"
          patbs           := Data.ByteString.pack (map (cast {to=Bits8}) pat)
          targetbs        := Data.ByteString.pack (map (cast {to=Bits8}) target)
        in matcher True patbs [targetbs] t) === [0,3,6]

||| prop_matchKMP:
|||
||| pat:    "AN"
||| target: "ANPANMAN"
|||
||| target   | A | N | P | A | N | M | A | N
||| index    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7
||| matchKMP | Y | N | N | Y | N | N | Y | N
|||
||| matchKMP "AN" "ANPANMAN" => [0, 3, 6]
|||
prop_matchKMP : Property
prop_matchKMP = property1 $
  let pat   := Prelude.unpack "AN"
      patbs := Data.ByteString.pack (map (cast {to=Bits8}) pat)
    in case decSo $ (not $ null patbs) of
         No  _      =>
           assert_total $ idris_crash "pat is null"
         Yes patprf =>
           let target   := Prelude.unpack "ANPANMAN"
               targetbs := Data.ByteString.pack (map (cast {to=Bits8}) target)
             in case decSo $ (not $ null targetbs) of
                  No  _         =>
                    assert_total $ idris_crash "target is null"
                  Yes targetprf =>
                    ( run1 $ \t =>
                        matchKMP patbs targetbs {prfpat=patprf} {prftarget=targetprf} t) === [0,3,6]

export
props : Group
props = MkGroup "KnuthMorrisPratt"
  [ ("prop_false_matcher", prop_false_matcher)
  , ("prop_true_matcher", prop_true_matcher)
  , ("prop_matchKMP", prop_matchKMP)
  ]
