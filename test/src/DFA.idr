module DFA

import Data.ByteString.Search.DFA

import Hedgehog
import Data.Array
import Data.ByteString
import Data.Fin
import Data.Linear.Ref1
import Data.Linear.Token
import Data.So
import Data.Vect

||| prop_matchDFA:
|||
||| pat:    "AN"
||| target: "ANPANMAN"
|||
||| target | A | N | P | A | N | M | A | N
||| index  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7
||| match  | Y | N | N | Y | N | N | Y | N
|||
||| matchDFA "AN" "ANPANMAN" => [0, 3, 6]
|||
prop_matchDFA : Property
prop_matchDFA = property1 $
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
                        matchDFA patbs targetbs {prfpat=patprf} {prftarget=targetprf} t) === [0,3,6]

||| prop_indicesDFA:
|||
||| pat:    "ABCABC"
||| target: "ABCABCABC"
|||
||| target | A | B | C | A | B | C | A | B | C
||| index  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8
||| match  | Y | N | N | Y | N | N | N | N | N
|||
||| indicesDFA "ABCABC" "ABCABCABC" => [0, 3]
|||
prop_indicesDFA : Property
prop_indicesDFA = property1 $
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
                        indicesDFA patbs targetbs {prfpat=patprf} {prftarget=targetprf} t) === [0,3]

||| prop_breakDFA:
|||
||| breakDFA "ABCABC" "ABCABCABC" => (empty, ABCABCABC)
|||
prop_breakDFA : Property
prop_breakDFA = property1 $
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
                            breakDFA patbs targetbs {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t) === ( Data.ByteString.empty
                                                                                                                       , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "ABCABCABC")
                                                                                                                       )

||| prop_breakAfterDFA:
|||
||| breakAfterDFA "ABCABC" "ABCABCABC" => (ABCABC, ABC)
|||
prop_breakAfterDFA : Property
prop_breakAfterDFA = property1 $
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
                            breakAfterDFA patbs targetbs {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t) === ( Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "ABCABC")
                                                                                                                            , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "ABC")
                                                                                                                            )


||| prop_splitKeepFrontDFA:
|||
||| splitKeepFrontDFA "ABCABC" "ABCABCABC" => [ABCABCABC]
|||
prop_splitKeepFrontDFA : Property
prop_splitKeepFrontDFA = property1 $
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
                            splitKeepFrontDFA patbs targetbs {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t) === [ Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "ABCABCABC")
                                                                                                                                ]

||| prop_splitKeepEndDFA:
|||
||| splitKeepEndDFA "ABCABC" "ABCABCABC" => [ABCABC, ABC]
|||
prop_splitKeepEndDFA : Property
prop_splitKeepEndDFA = property1 $
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
                            splitKeepEndDFA patbs targetbs {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t) === [ Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "ABCABC")
                                                                                                                              , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "ABC")
                                                                                                                              ]

||| prop_splitDropDFA:
|||
||| splitDropDFA "ABCABC" "ABCABCABC" => [empty, ABC]
|||
prop_splitDropDFA : Property
prop_splitDropDFA = property1 $
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
                            splitDropDFA patbs targetbs {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t) === [ Data.ByteString.empty
                                                                                                                           , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "ABC")
                                                                                                                           ]

||| prop_replaceDFA:
|||
||| replaceDFA "AB" "BA" ABCABCABC" => [BA, C, BA, C , BA, C]
|||
prop_replaceDFA : Property
prop_replaceDFA = property1 $
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
                            replaceDFA patbs subbs targetbs {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t) === [ Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "BA")
                                                                                                                               , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "C")
                                                                                                                               , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "BA")
                                                                                                                               , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "C")
                                                                                                                               , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "BA")
                                                                                                                               , Data.ByteString.pack $ map (cast {to=Bits8}) (Prelude.unpack "C")
                                                                                                                               ]

export
props : Group
props = MkGroup "DFA"
  [ ("prop_matchDFA", prop_matchDFA)
  , ("prop_indicesDFA", prop_indicesDFA)
  , ("prop_breakDFA", prop_breakDFA)
  , ("prop_breakAfterDFA", prop_breakAfterDFA)
  , ("prop_splitKeepFrontDFA", prop_splitKeepFrontDFA)
  , ("prop_splitKeepEndDFA", prop_splitKeepEndDFA)
  , ("prop_splitDropDFA", prop_splitDropDFA)
  , ("prop_replaceDFA", prop_replaceDFA)
  ]
