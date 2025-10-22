module Utils

import Hedgehog
import Data.Array
import Data.ByteString
import Data.ByteString.Search.Internal.Utils
import Data.Linear.Ref1
import Data.Linear.Token

prop_kmpBorders : Property
prop_kmpBorders = property1 $
  ( run1 $ \t =>
      let pat             := Prelude.unpack "ANPANMAN"
          patbs           := Data.ByteString.pack (map (cast {to=Bits8}) pat)
          kmpborders  # t := kmpBorders patbs t
          kmpborders' # t := Data.Array.Core.freeze kmpborders t
        in Prelude.Interfaces.toList kmpborders' # t ) === [0,0,0,0,1,2,0,1,2]

export
props : Group
props = MkGroup "Utils"
  [ ("prop_kmpBorders", prop_kmpBorders)
  ]
