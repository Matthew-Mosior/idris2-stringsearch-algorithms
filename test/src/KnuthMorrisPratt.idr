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
||| target | A | N | P | A | N | M | A | N
||| index  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7
||| match  | Y | N | N | Y | N | N | Y | N
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
||| target | A | B | C | A | B | C | A | B | C
||| index  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8
||| match  | Y | N | N | Y | N | N | N | N | N
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

||| prop_breakKMP:
|||
||| breakKMP "ABCABC" "ABCABCABC" => (empty, ABCABCABC)
|||
prop_breakKMP : Property
prop_breakKMP = property1 $
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
                            breakKMP patbs targetbs {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t) === ( Data.ByteString.empty
                                                                                                                       , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "ABCABCABC")
                                                                                                                       )

||| prop_breakAfterKMP:
|||
||| breakAfterKMP "ABCABC" "ABCABCABC" => (ABCABC, ABC)
|||
prop_breakAfterKMP : Property
prop_breakAfterKMP = property1 $
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
                            breakAfterKMP patbs targetbs {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t) === ( Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "ABCABC")
                                                                                                                            , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "ABC")
                                                                                                                            )


||| prop_splitKeepFrontKMP:
|||
||| splitKeepFrontKMP "ABCABC" "ABCABCABC" => [ABCABCABC]
|||
prop_splitKeepFrontKMP : Property
prop_splitKeepFrontKMP = property1 $
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
                            splitKeepFrontKMP patbs targetbs {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t) === [ Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "ABCABCABC")
                                                                                                                                ]

||| prop_splitKeepEndKMP:
|||
||| splitKeepEndKMP "ABCABC" "ABCABCABC" => [ABCABC, ABC]
|||
prop_splitKeepEndKMP : Property
prop_splitKeepEndKMP = property1 $
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
                            splitKeepEndKMP patbs targetbs {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t) === [ Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "ABCABC")
                                                                                                                              , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "ABC")
                                                                                                                              ]

||| prop_splitDropKMP:
|||
||| splitDropKMP "ABCABC" "ABCABCABC" => [empty, ABC]
|||
prop_splitDropKMP : Property
prop_splitDropKMP = property1 $
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
                            splitDropKMP patbs targetbs {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t) === [ Data.ByteString.empty
                                                                                                                           , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "ABC")
                                                                                                                           ]

||| prop_replaceKMP:
|||
||| replaceKMP "AB" "BA" ABCABCABC" => [BA, C, BA, C , BA, C]
|||
prop_replaceKMP : Property
prop_replaceKMP = property1 $
  let pat   := Prelude.unpack "AB"
      patbs := Data.ByteString.pack (map (cast {to=Bits8}) pat)
    in case decSo $ (not $ null patbs) of
         No  _      =>
           assert_total $ idris_crash "pat is null"
         Yes patprf =>
           let sub      := Prelude.unpack "BA"
               subbs    := Data.ByteString.pack (map (cast {to=Bits8}) sub)
               target   := Prelude.unpack "ABCABCABC"
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
                            replaceKMP patbs subbs targetbs {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t) === [ Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "BA")
                                                                                                                               , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "C")
                                                                                                                               , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "BA")
                                                                                                                               , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "C")
                                                                                                                               , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "BA")
                                                                                                                               , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "C")
                                                                                                                               ]

export
props : Group
props = MkGroup "KnuthMorrisPratt"
  [ ("prop_matchKMP", prop_matchKMP)
  , ("prop_indicesKMP", prop_indicesKMP)
  , ("prop_breakKMP", prop_breakKMP)
  , ("prop_breakAfterKMP", prop_breakAfterKMP)
  , ("prop_splitKeepFrontKMP", prop_splitKeepFrontKMP)
  , ("prop_splitKeepEndKMP", prop_splitKeepEndKMP)
  , ("prop_splitDropKMP", prop_splitDropKMP)
  , ("prop_replaceKMP", prop_replaceKMP)
  ]
