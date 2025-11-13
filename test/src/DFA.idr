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

export
props : Group
props = MkGroup "DFA"
  [ ("prop_matchDFA", prop_matchDFA)
  , ("prop_indicesDFA", prop_indicesDFA)
  ]
