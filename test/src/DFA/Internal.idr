module DFA.Internal

import Data.Array.Core
import Data.ByteString
import Data.ByteString.Search.DFA.Internal
import Data.Enum
import Data.Linear.Ref1
import Data.Linear.Token
import Hedgehog

%default total

||| Verify that DFA state 0 and byte 65 flatten to transition-table index 65.
|||
prop_dfaIndex_0_65 : Property
prop_dfaIndex_0_65 =
  property1 $
    let state : DFAState 7
        state = 0

        actual : Bits32
        actual = cast $ dfaIndex (MkDFAIndex state 65)

     in actual === 65

||| Verify that DFA state 1 and byte 65 flatten to transition-table index 321.
|||
prop_dfaIndex_1_65 : Property
prop_dfaIndex_1_65 =
  property1 $
    let state : DFAState 7
        state = 1

        actual : Bits32
        actual = cast $ dfaIndex (MkDFAIndex state 65)

     in actual === 321

||| Verify that DFA state 1 and byte 66 flatten to transition-table index 322.
|||
prop_dfaIndex_1_66 : Property
prop_dfaIndex_1_66 =
  property1 $
    let state : DFAState 7
        state = 1

        actual : Bits32
        actual = cast $ dfaIndex (MkDFAIndex state 66)

     in actual === 322

||| Verify that DFA state 2 and byte 67 flatten to transition-table index 579.
|||
prop_dfaIndex_2_67 : Property
prop_dfaIndex_2_67 =
  property1 $
    let state : DFAState 7
        state = 2

        actual : Bits32
        actual = cast $ dfaIndex (MkDFAIndex state 67)

     in actual === 579

||| Verify that DFA state 6 and byte 65 flatten to transition-table index 1601.
|||
prop_dfaIndex_6_65 : Property
prop_dfaIndex_6_65 =
  property1 $
    let state : DFAState 7
        state = 6

        actual : Bits32
        actual = cast $ dfaIndex (MkDFAIndex state 65)

     in actual === 1601

||| Verify that DFA state 6 and byte 67 flatten to transition-table index 1603.
|||
prop_dfaIndex_6_67 : Property
prop_dfaIndex_6_67 =
  property1 $
    let state : DFAState 7
        state = 6

        actual : Bits32
        actual = cast $ dfaIndex (MkDFAIndex state 67)

     in actual === 1603

||| Verify that a DFA transition can be written and read using the
||| check-free bounded indexing representation.
|||
prop_dfaTransition_0_A_1 : Property
prop_dfaTransition_0_A_1 =
  property1 $ do
    ( run1 $ \t =>
        let table # t := newDFATable {states = 7} t
            state0 : DFAState 7
            state0 = 0
            state1 : DFAState 7
            state1 = 1
            _ # t :=
              setDFATransition
                table
                state0
                65
                state1
                t
            next # t :=
              dfaTransition
                table
                state0
                65
                t
          in dfaStateValue next # t ) === 1

||| Verify several transitions corresponding to the `"ABCABC"` DFA.
|||
prop_dfaTransitions_ABCABC : Property
prop_dfaTransitions_ABCABC =
  property1 $ do
    ( run1 $ \t =>
        let table # t := newDFATable {states = 7} t
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
            _ # t := setDFATransition table s0 65 s1 t
            _ # t := setDFATransition table s1 66 s2 t
            _ # t := setDFATransition table s2 67 s3 t
            _ # t := setDFATransition table s3 65 s4 t
            _ # t := setDFATransition table s4 66 s5 t
            _ # t := setDFATransition table s5 67 s6 t
            r0 # t := dfaTransition table s0 65 t
            r1 # t := dfaTransition table s1 66 t
            r2 # t := dfaTransition table s2 67 t
            r3 # t := dfaTransition table s3 65 t
            r4 # t := dfaTransition table s4 66 t
            r5 # t := dfaTransition table s5 67 t
          in (dfaStateValue r0, dfaStateValue r1, dfaStateValue r2, dfaStateValue r3, dfaStateValue r4, dfaStateValue r5) # t ) === (the Bits32 1, the Bits32 2, the Bits32 3, the Bits32 4, the Bits32 5, the Bits32 6)

||| prop_automaton : "ANPANMAN"
|||
||| | flat index | value | meaning (decoded) |
||| | ---------- | ----- | ----------------- |
||| | 65         | 1     | δ(0, 'A') = 1     |
||| | 321        | 1     | δ(1, 'A') = 1     |
||| | 334        | 2     | δ(1, 'N') = 2     |
||| | 577        | 1     | δ(2, 'A') = 1     |
||| | 592        | 3     | δ(2, 'P') = 3     |
||| | 833        | 4     | δ(3, 'A') = 4     |
||| | 1089       | 1     | δ(4, 'A') = 1     |
||| | 1102       | 5     | δ(4, 'N') = 5     |
||| | 1345       | 1     | δ(5, 'A') = 1     |
||| | 1357       | 6     | δ(5, 'M') = 6     |
||| | 1601       | 7     | δ(6, 'A') = 7     |
||| | 1857       | 1     | δ(7, 'A') = 1     |
||| | 1870       | 8     | δ(7, 'N') = 8     |
||| | 2113       | 1     | δ(8, 'A') = 1     |
|||
prop_automaton : Property
prop_automaton =
  property1 $ do
    ( run1 $ \t =>
        let pat :=
              Prelude.unpack "ANPANMAN"

            patbs :=
              Data.ByteString.pack
                (map (cast {to=Bits8}) pat)

            automaton' # t :=
              automaton patbs t

         in case automaton' of
              Nothing =>
                (the (List (Bits32, Bits32)) []) # t

              Just (MkDFAutomaton stspace table) =>
                let Just s0 := tryIndex {r = stspace.states} 0
                      | Nothing =>
                          (the (List (Bits32, Bits32)) []) # t

                    Just s1 := tryIndex {r = stspace.states} 1
                      | Nothing =>
                          (the (List (Bits32, Bits32)) []) # t

                    Just s2 := tryIndex {r = stspace.states} 2
                      | Nothing =>
                          (the (List (Bits32, Bits32)) []) # t

                    Just s3 := tryIndex {r = stspace.states} 3
                      | Nothing =>
                          (the (List (Bits32, Bits32)) []) # t

                    Just s4 := tryIndex {r = stspace.states} 4
                      | Nothing =>
                          (the (List (Bits32, Bits32)) []) # t

                    Just s5 := tryIndex {r = stspace.states} 5
                      | Nothing =>
                          (the (List (Bits32, Bits32)) []) # t

                    Just s6 := tryIndex {r = stspace.states} 6
                      | Nothing =>
                          (the (List (Bits32, Bits32)) []) # t

                    Just s7 := tryIndex {r = stspace.states} 7
                      | Nothing =>
                          (the (List (Bits32, Bits32)) []) # t

                    Just s8 := tryIndex {r = stspace.states} 8
                      | Nothing =>
                          (the (List (Bits32, Bits32)) []) # t

                    r0  # t := dfaTransition {statesPrf = stspace.statesBounded} table s0 65 t
                    r1  # t := dfaTransition {statesPrf = stspace.statesBounded} table s1 65 t
                    r2  # t := dfaTransition {statesPrf = stspace.statesBounded} table s1 78 t
                    r3  # t := dfaTransition {statesPrf = stspace.statesBounded} table s2 65 t
                    r4  # t := dfaTransition {statesPrf = stspace.statesBounded} table s2 80 t
                    r5  # t := dfaTransition {statesPrf = stspace.statesBounded} table s3 65 t
                    r6  # t := dfaTransition {statesPrf = stspace.statesBounded} table s4 65 t
                    r7  # t := dfaTransition {statesPrf = stspace.statesBounded} table s4 78 t
                    r8  # t := dfaTransition {statesPrf = stspace.statesBounded} table s5 65 t
                    r9  # t := dfaTransition {statesPrf = stspace.statesBounded} table s5 77 t
                    r10 # t := dfaTransition {statesPrf = stspace.statesBounded} table s6 65 t
                    r11 # t := dfaTransition {statesPrf = stspace.statesBounded} table s7 65 t
                    r12 # t := dfaTransition {statesPrf = stspace.statesBounded} table s7 78 t
                    r13 # t := dfaTransition {statesPrf = stspace.statesBounded} table s8 65 t

                 in [ (65,   dfaStateValue r0)
                    , (321,  dfaStateValue r1)
                    , (334,  dfaStateValue r2)
                    , (577,  dfaStateValue r3)
                    , (592,  dfaStateValue r4)
                    , (833,  dfaStateValue r5)
                    , (1089, dfaStateValue r6)
                    , (1102, dfaStateValue r7)
                    , (1345, dfaStateValue r8)
                    , (1357, dfaStateValue r9)
                    , (1601, dfaStateValue r10)
                    , (1857, dfaStateValue r11)
                    , (1870, dfaStateValue r12)
                    , (2113, dfaStateValue r13)
                    ]
                    # t ) === [ (65,   1)
                              , (321,  1)
                              , (334,  2)
                              , (577,  1)
                              , (592,  3)
                              , (833,  4)
                              , (1089, 1)
                              , (1102, 5)
                              , (1345, 1)
                              , (1357, 6)
                              , (1601, 7)
                              , (1857, 1)
                              , (1870, 8)
                              , (2113, 1)
                              ]

||| prop_automaton' : "ABCABC"
|||
||| | flat index | value | meaning      |
||| | ---------- | ----- | ------------ |
||| |         65 |     1 | δ(0,'A') = 1 |
||| |        321 |     1 | δ(1,'A') = 1 |
||| |        322 |     2 | δ(1,'B') = 2 |
||| |        577 |     1 | δ(2,'A') = 1 |
||| |        579 |     3 | δ(2,'C') = 3 |
||| |        833 |     4 | δ(3,'A') = 4 |
||| |       1089 |     1 | δ(4,'A') = 1 |
||| |       1090 |     5 | δ(4,'B') = 5 |
||| |       1345 |     1 | δ(5,'A') = 1 |
||| |       1347 |     6 | δ(5,'C') = 6 |
||| |       1601 |     1 | δ(6,'A') = 1 |
|||
prop_automaton' : Property
prop_automaton' =
  property1 $ do
    ( run1 $ \t =>
        let pat :=
              Prelude.unpack "ABCABC"

            patbs :=
              Data.ByteString.pack
                (map (cast {to=Bits8}) pat)

            automaton' # t :=
              automaton patbs t

         in case automaton' of
              Nothing =>
                (the (List (Bits32, Bits32)) []) # t

              Just (MkDFAutomaton stspace table) =>
                let Just s0 := tryIndex {r = stspace.states} 0
                      | Nothing =>
                          (the (List (Bits32, Bits32)) []) # t

                    Just s1 := tryIndex {r = stspace.states} 1
                      | Nothing =>
                          (the (List (Bits32, Bits32)) []) # t

                    Just s2 := tryIndex {r = stspace.states} 2
                      | Nothing =>
                          (the (List (Bits32, Bits32)) []) # t

                    Just s3 := tryIndex {r = stspace.states} 3
                      | Nothing =>
                          (the (List (Bits32, Bits32)) []) # t

                    Just s4 := tryIndex {r = stspace.states} 4
                      | Nothing =>
                          (the (List (Bits32, Bits32)) []) # t

                    Just s5 := tryIndex {r = stspace.states} 5
                      | Nothing =>
                          (the (List (Bits32, Bits32)) []) # t

                    Just s6 := tryIndex {r = stspace.states} 6
                      | Nothing =>
                          (the (List (Bits32, Bits32)) []) # t

                    r0  # t := dfaTransition {statesPrf = stspace.statesBounded} table s0 65 t
                    r1  # t := dfaTransition {statesPrf = stspace.statesBounded} table s1 65 t
                    r2  # t := dfaTransition {statesPrf = stspace.statesBounded} table s1 66 t
                    r3  # t := dfaTransition {statesPrf = stspace.statesBounded} table s2 65 t
                    r4  # t := dfaTransition {statesPrf = stspace.statesBounded} table s2 67 t
                    r5  # t := dfaTransition {statesPrf = stspace.statesBounded} table s3 65 t
                    r6  # t := dfaTransition {statesPrf = stspace.statesBounded} table s4 65 t
                    r7  # t := dfaTransition {statesPrf = stspace.statesBounded} table s4 66 t
                    r8  # t := dfaTransition {statesPrf = stspace.statesBounded} table s5 65 t
                    r9  # t := dfaTransition {statesPrf = stspace.statesBounded} table s5 67 t
                    r10 # t := dfaTransition {statesPrf = stspace.statesBounded} table s6 65 t

                 in [ (65,   dfaStateValue r0)
                    , (321,  dfaStateValue r1)
                    , (322,  dfaStateValue r2)
                    , (577,  dfaStateValue r3)
                    , (579,  dfaStateValue r4)
                    , (833,  dfaStateValue r5)
                    , (1089, dfaStateValue r6)
                    , (1090, dfaStateValue r7)
                    , (1345, dfaStateValue r8)
                    , (1347, dfaStateValue r9)
                    , (1601, dfaStateValue r10)
                    ]
                    # t ) === [ (65,   1)
                              , (321,  1)
                              , (322,  2)
                              , (577,  1)
                              , (579,  3)
                              , (833,  4)
                              , (1089, 1)
                              , (1090, 5)
                              , (1345, 1)
                              , (1347, 6)
                              , (1601, 1)
                              ]

export
props : Group
props =
  MkGroup "DFA.Internal"
    [ ("prop_dfaIndex_0_65", prop_dfaIndex_0_65)
    , ("prop_dfaIndex_1_65", prop_dfaIndex_1_65)
    , ("prop_dfaIndex_1_66", prop_dfaIndex_1_66)
    , ("prop_dfaIndex_2_67", prop_dfaIndex_2_67)
    , ("prop_dfaIndex_6_65", prop_dfaIndex_6_65)
    , ("prop_dfaIndex_6_67", prop_dfaIndex_6_67)
    , ("prop_dfaTransition_0_A_1", prop_dfaTransition_0_A_1)
    , ("prop_dfaTransitions_ABCABC", prop_dfaTransitions_ABCABC)
    , ("prop_automaton", prop_automaton)
    , ("prop_automaton'", prop_automaton')
    ]
