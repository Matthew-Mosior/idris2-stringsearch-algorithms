module Utils

import Hedgehog
import Data.Array
import Data.ByteString
import Data.ByteString.Search.Internal.Utils
import Data.Fin
import Data.Linear.Ref1
import Data.Linear.Token
import Data.Vect

prop_kmpBorders : Property
prop_kmpBorders = property1 $
  ( run1 $ \t =>
      let pat             := Prelude.unpack "ANPANMAN"
          patbs           := Data.ByteString.pack (map (cast {to=Bits8}) pat)
          kmpborders  # t := kmpBorders patbs t
          kmpborders' # t := Data.Array.Core.freeze kmpborders t
        in Prelude.Interfaces.toList kmpborders' # t ) === [0,0,0,0,1,2,0,1,2]

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
