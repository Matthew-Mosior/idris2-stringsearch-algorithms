module KnuthMorrisPratt.Internal

import Data.ByteString
import Data.ByteString.Search.DFA.Types
import Data.ByteString.Search.KnuthMorrisPratt.Internal
import Data.Enum
import Data.Linear.Ref1
import Data.Linear.Token
import Hedgehog

%default total

||| Verify that a KMP border value can be written and read using the
||| bounded state representation.
|||
prop_kmpBorder_0_0 : Property
prop_kmpBorder_0_0 =
  property1 $ do
    ( run1 $ \t =>
        let table # t :=
              newKMPBorderTable {states = 7} t

            s0 : DFAState 7
            s0 = 0

            _ # t :=
              setKMPBorder
                table
                s0
                s0
                t

            result # t :=
              kmpBorder
                table
                s0
                t

         in dfaStateValue result # t ) === the Bits32 0

||| Verify that a nonzero KMP border value can be written and read using
||| the bounded state representation.
|||
prop_kmpBorder_4_1 : Property
prop_kmpBorder_4_1 =
  property1 $ do
    ( run1 $ \t =>
        let table # t :=
              newKMPBorderTable {states = 7} t

            s4 : DFAState 7
            s4 = 4

            s1 : DFAState 7
            s1 = 1

            _ # t :=
              setKMPBorder
                table
                s4
                s1
                t

            result # t :=
              kmpBorder
                table
                s4
                t

         in dfaStateValue result # t ) === the Bits32 1

||| Verify several manually written KMP border values.
|||
||| These values correspond to the `"ABCABC"` border table:
|||
||| Indices: 0  1  2  3  4  5  6
||| Borders: 0  0  0  0  1  2  3
|||
prop_kmpBorders_ABCABC_manual : Property
prop_kmpBorders_ABCABC_manual =
  property1 $ do
    ( run1 $ \t =>
        let table # t :=
              newKMPBorderTable {states = 7} t

            s0 : DFAState 7
            s0 = 0

            s1 : DFAState 7
            s1 = 1

            s2 : DFAState 7
            s2 = 2

            s3 : DFAState 7
            s3 = 3

            s4 : DFAState 7
            s4 = 4

            s5 : DFAState 7
            s5 = 5

            s6 : DFAState 7
            s6 = 6

            _ # t := setKMPBorder table s0 s0 t
            _ # t := setKMPBorder table s1 s0 t
            _ # t := setKMPBorder table s2 s0 t
            _ # t := setKMPBorder table s3 s0 t
            _ # t := setKMPBorder table s4 s1 t
            _ # t := setKMPBorder table s5 s2 t
            _ # t := setKMPBorder table s6 s3 t

            r0 # t := kmpBorder table s0 t
            r1 # t := kmpBorder table s1 t
            r2 # t := kmpBorder table s2 t
            r3 # t := kmpBorder table s3 t
            r4 # t := kmpBorder table s4 t
            r5 # t := kmpBorder table s5 t
            r6 # t := kmpBorder table s6 t

         in ( dfaStateValue r0
            , dfaStateValue r1
            , dfaStateValue r2
            , dfaStateValue r3
            , dfaStateValue r4
            , dfaStateValue r5
            , dfaStateValue r6
            )
            # t ) === ( the Bits32 0
                      , the Bits32 0
                      , the Bits32 0
                      , the Bits32 0
                      , the Bits32 1
                      , the Bits32 2
                      , the Bits32 3
                      )

||| Verify the KMP border table generated for `"ANPANMAN"`.
|||
||| Expected border table:
|||
||| Indices: 0  1  2  3  4  5  6  7  8
||| Borders: 0  0  0  0  1  2  0  1  2
|||
prop_kmpBorders_ANPANMAN : Property
prop_kmpBorders_ANPANMAN =
  property1 $ do
    ( run1 $ \t =>
        let pat :=
              Prelude.unpack "ANPANMAN"

            patbs :=
              Data.ByteString.pack
                (map (cast {to=Bits8}) pat)

            bords # t :=
              kmpBorders patbs t

         in case bords of
              Nothing =>
                (the (List Bits32) []) # t

              Just (MkKMPBorders stspace table) =>
                let Just s0 := tryIndex {r = stspace.states} 0
                      | Nothing =>
                          (the (List Bits32) []) # t

                    Just s1 := tryIndex {r = stspace.states} 1
                      | Nothing =>
                          (the (List Bits32) []) # t

                    Just s2 := tryIndex {r = stspace.states} 2
                      | Nothing =>
                          (the (List Bits32) []) # t

                    Just s3 := tryIndex {r = stspace.states} 3
                      | Nothing =>
                          (the (List Bits32) []) # t

                    Just s4 := tryIndex {r = stspace.states} 4
                      | Nothing =>
                          (the (List Bits32) []) # t

                    Just s5 := tryIndex {r = stspace.states} 5
                      | Nothing =>
                          (the (List Bits32) []) # t

                    Just s6 := tryIndex {r = stspace.states} 6
                      | Nothing =>
                          (the (List Bits32) []) # t

                    Just s7 := tryIndex {r = stspace.states} 7
                      | Nothing =>
                          (the (List Bits32) []) # t

                    Just s8 := tryIndex {r = stspace.states} 8
                      | Nothing =>
                          (the (List Bits32) []) # t

                    r0 # t := kmpBorder table s0 t
                    r1 # t := kmpBorder table s1 t
                    r2 # t := kmpBorder table s2 t
                    r3 # t := kmpBorder table s3 t
                    r4 # t := kmpBorder table s4 t
                    r5 # t := kmpBorder table s5 t
                    r6 # t := kmpBorder table s6 t
                    r7 # t := kmpBorder table s7 t
                    r8 # t := kmpBorder table s8 t

                 in [ dfaStateValue r0
                    , dfaStateValue r1
                    , dfaStateValue r2
                    , dfaStateValue r3
                    , dfaStateValue r4
                    , dfaStateValue r5
                    , dfaStateValue r6
                    , dfaStateValue r7
                    , dfaStateValue r8
                    ]
                    # t ) === [ 0
                              , 0
                              , 0
                              , 0
                              , 1
                              , 2
                              , 0
                              , 1
                              , 2
                              ]

||| Verify the KMP border table generated for `"ABCABC"`.
|||
||| Expected border table:
|||
||| Indices: 0  1  2  3  4  5  6
||| Borders: 0  0  0  1  2  3  3
|||
||| Note that the exact expected values should match the semantics of the
||| current `kmpBorders` implementation rather than the transition table.
|||
prop_kmpBorders_ABCABC : Property
prop_kmpBorders_ABCABC =
  property1 $ do
    ( run1 $ \t =>
        let pat :=
              Prelude.unpack "ABCABC"

            patbs :=
              Data.ByteString.pack
                (map (cast {to=Bits8}) pat)

            bords # t :=
              kmpBorders patbs t

         in case bords of
              Nothing =>
                (the (List Bits32) []) # t

              Just (MkKMPBorders stspace table) =>
                let Just s0 := tryIndex {r = stspace.states} 0
                      | Nothing =>
                          (the (List Bits32) []) # t

                    Just s1 := tryIndex {r = stspace.states} 1
                      | Nothing =>
                          (the (List Bits32) []) # t

                    Just s2 := tryIndex {r = stspace.states} 2
                      | Nothing =>
                          (the (List Bits32) []) # t

                    Just s3 := tryIndex {r = stspace.states} 3
                      | Nothing =>
                          (the (List Bits32) []) # t

                    Just s4 := tryIndex {r = stspace.states} 4
                      | Nothing =>
                          (the (List Bits32) []) # t

                    Just s5 := tryIndex {r = stspace.states} 5
                      | Nothing =>
                          (the (List Bits32) []) # t

                    Just s6 := tryIndex {r = stspace.states} 6
                      | Nothing =>
                          (the (List Bits32) []) # t

                    r0 # t := kmpBorder table s0 t
                    r1 # t := kmpBorder table s1 t
                    r2 # t := kmpBorder table s2 t
                    r3 # t := kmpBorder table s3 t
                    r4 # t := kmpBorder table s4 t
                    r5 # t := kmpBorder table s5 t
                    r6 # t := kmpBorder table s6 t

                 in [ dfaStateValue r0
                    , dfaStateValue r1
                    , dfaStateValue r2
                    , dfaStateValue r3
                    , dfaStateValue r4
                    , dfaStateValue r5
                    , dfaStateValue r6
                    ]
                    # t ) === [ 0
                              , 0
                              , 0
                              , 0
                              , 1
                              , 2
                              , 3
                              ]

export
props : Group
props =
  MkGroup "KnuthMorrisPratt.Internal"
    [ ("prop_kmpBorder_0_0", prop_kmpBorder_0_0)
    , ("prop_kmpBorder_4_1", prop_kmpBorder_4_1)
    , ("prop_kmpBorders_ABCABC_manual", prop_kmpBorders_ABCABC_manual)
    , ("prop_kmpBorders_ANPANMAN", prop_kmpBorders_ANPANMAN)
    , ("prop_kmpBorders_ABCABC", prop_kmpBorders_ABCABC)
    ]
