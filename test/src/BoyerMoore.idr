module BoyerMoore

import Data.ByteString.Search.BoyerMoore

import Hedgehog
import Data.Array
import Data.ByteString
import Data.Fin
import Data.Linear.Ref1
import Data.Linear.Token
import Data.So
import Data.Vect

||| prop_matchBM:
|||
||| pat:    "AN"
||| target: "ANPANMAN"
|||
||| target | A | N | P | A | N | M | A | N
||| index  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7
||| match  | Y | N | N | Y | N | N | Y | N
|||
||| matchBM "AN" "ANPANMAN" => [0, 3, 6]
|||
prop_matchBM : Property
prop_matchBM = property1 $
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
                    case decSo $ (length targetbs) >= (length patbs) of
                      No  _         =>
                        assert_total $ idris_crash "the target is shorter than the pattern"
                      Yes lengthprf =>
                        ( run1 $ \t =>
                            matchBM patbs targetbs {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t) === [0,3,6]

||| prop_indicesBM:
|||
||| pat:    "ABCABC"
||| target: "ABCABCABC"
|||
||| target | A | B | C | A | B | C | A | B | C
||| index  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8
||| match  | Y | N | N | Y | N | N | N | N | N
|||
||| indicesBM "ABCABC" "ABCABCABC" => [0, 3]
|||
prop_indicesBM : Property
prop_indicesBM = property1 $
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
                    case decSo $ (length targetbs) >= (length patbs) of
                      No  _         =>
                        assert_total $ idris_crash "the target is shorter than the pattern"
                      Yes lengthprf =>
                        ( run1 $ \t =>
                            indicesBM patbs targetbs {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t) === [0,3]

||| prop_breakBM:
|||
||| breakBM "ABCABC" "ABCABCABC" => (empty, ABCABCABC)
|||
prop_breakBM : Property
prop_breakBM = property1 $
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
                    case decSo $ (length targetbs) >= (length patbs) of
                      No  _         =>
                        assert_total $ idris_crash "the target is shorter than the pattern"
                      Yes lengthprf =>
                        ( run1 $ \t =>
                            breakBM patbs targetbs {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t) === (Data.ByteString.empty, Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "ABCABCABC"))

export
props : Group
props = MkGroup "BoyerMoore"
  [ ("prop_matchBM", prop_matchBM)
  , ("prop_indicesBM", prop_indicesBM)
  , ("prop_breakBM", prop_breakBM)
  ]
