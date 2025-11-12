module KnuthMorrisPratt

import Data.ByteString.Search.KnuthMorrisPratt

import Hedgehog
import Data.Array
import Data.ByteString
import Data.Fin
import Data.Linear.Ref1
import Data.Linear.Token
import Data.So
import Data.Vect

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

||| prop_indicesKMP:
|||
||| pat:    "ABCABC"
||| target: "ABCABCABC"
|||
||| target     | A | B | C | A | B | C | A | B | C
||| index      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8
||| indicesKMP | Y | N | N | Y | N | N | N | N | N
|||
||| indicesKMP "ABCABC" "ABCABCABC" => [0, 3]
|||
prop_indicesKMP : Property
prop_indicesKMP = property1 $
  let pat   := Prelude.unpack "ABCABC"
      patbs := Data.ByteString.pack (map (cast {to=Bits8}) pat)
    in case decSo $ (not $ null patbs) of
         No  _      =>
           assert_total $ idris_crash "pat is null"
         Yes patprf =>
           let target   := Prelude.unpack "ABCABCABC"
               targetbs := Data.ByteString.pack (map (cast {to=Bits8}) target)
             in case decSo $ (not $ null targetbs) of
                  No  _         =>
                    assert_total $ idris_crash "target is null"
                  Yes targetprf =>
                    ( run1 $ \t =>
                        indicesKMP patbs targetbs {prfpat=patprf} {prftarget=targetprf} t) === [0,3]

export
props : Group
props = MkGroup "KnuthMorrisPratt"
  [ ("prop_matchKMP", prop_matchKMP)
  , ("prop_indicesKMP", prop_indicesKMP)
  ]
