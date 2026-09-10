||| Utilities for the DFA string searching algorithm.
module Data.ByteString.Search.DFA.Internal

import Data.Array.Core
import Data.Bits
import Data.ByteString
import Data.ByteString.Search.DFA.Types
import Data.ByteString.Search.KnuthMorrisPratt.Internal
import Data.DArray
import Data.Enum
import Data.Linear.Ref1

%hide Data.Buffer.Core.get
%hide Data.Buffer.Core.set
%hide Data.List.Elem.get

%default total

||| Builds a deterministic finite automaton (DFA) for pattern matching over a
||| `ByteString`.
|||
||| The automaton encodes transitions from `(state, input byte)` to the next
||| DFA state.
|||
||| Unlike the previous implementation, transition-table positions and
||| transition values are represented by bounded `Index` values. Bounds are
||| established while constructing the automaton and are erased at runtime.
|||
||| The resulting search-time transition path therefore requires no
||| `tryNatToFin`, `tryIndex`, or other dynamic DFA-table bounds conversion.
|||
export
automaton :  (bs : ByteString)
          -> F1 s (Maybe (DFAutomaton s))
automaton bs t =
   let bord                          # t := kmpBorders bs t
       Just (MkKMPBorders stspace bord') := bord
         | Nothing =>
             Nothing # t
       arr                           # t := newDFATable {states = stspace.states} {statesPrf = stspace.statesBounded} t
       result                        # t := go stspace Z arr bord' t
       Just result'                      := result
         | Nothing =>
             Nothing # t
     in Just (MkDFAutomaton stspace result') # t
  where
    fillState :  (space : DFAStateSpace)
              -> (state : DFAState space.states)
              -> (byte : Bits8)
              -> (patbyte : Maybe Bits8)
              -> (bordcur : DFAState space.states)
              -> (arr : DFATable s space.states)
              -> F1 s (Maybe (DFATable s space.states))
    fillState space state byte patbyte bordcur arr t =
      let stateval      := dfaStateValue state
          Just patbyte' := patbyte
            | Nothing =>
                let False        := stateval == 0
                      | True =>
                          let zero   := zeroDFAState space
                              () # t := setDFATransition {statesPrf = space.statesBounded} arr state byte zero t
                              True   := byte == 0
                                | False =>
                                    assert_total (fillState space state (byte - 1) patbyte bordcur arr t)
                            in Just arr # t
                    bordcur' # t := dfaTransition {statesPrf = space.statesBounded} arr bordcur byte t
                    ()       # t := setDFATransition {statesPrf = space.statesBounded} arr state byte bordcur' t
                    True         := byte == 0
                      | False =>
                          assert_total (fillState space state (byte - 1) patbyte bordcur' arr t)
                  in Just arr # t
          False         := byte == patbyte'
            | True =>
                let Just next := toDFAState space (S $ cast stateval)
                      | Nothing =>
                          Nothing # t
                    ()    # t := setDFATransition {statesPrf = space.statesBounded} arr state byte next t
                    True      := byte == 0
                      | False =>
                          assert_total (fillState space state (byte - 1) patbyte bordcur arr t)
                  in Just arr # t
          False         := stateval == 0
            | True =>
                let zero   := zeroDFAState space
                    () # t := setDFATransition {statesPrf = space.statesBounded} arr state byte zero t
                    True   := byte == 0
                      | False =>
                          assert_total (fillState space state (byte - 1) patbyte bordcur arr t)
                  in Just arr # t
          bordcur'  # t := dfaTransition {statesPrf = space.statesBounded} arr bordcur byte t
          ()        # t := setDFATransition {statesPrf = space.statesBounded} arr state byte bordcur' t
          True          := byte == 0
            | False =>
                assert_total (fillState space state (byte - 1) patbyte bordcur' arr t)
        in Just arr # t
    ||| Construct the transition rows for each DFA state.
    |||
    ||| The KMP border table and DFA transition table share the same bounded
    ||| state space, so border values can be consumed directly as DFA states
    ||| without any intermediate `Nat` or `Fin` conversion.
    |||
    go :  (stspace : DFAStateSpace)
       -> (state : Nat)
       -> (arr : DFATable s stspace.states)
       -> (bord : KMPBorderTable s stspace.states)
       -> F1 s (Maybe (DFATable s stspace.states))
    go stspace state arr bord t =
      let False          := state > length bs
            | True =>
                Just arr # t
          Just state' := toDFAState stspace state
            | Nothing =>
                Nothing # t
          bordcur # t := kmpBorder bord state' t
          patbyte        := index state bs
          arr'       # t := fillState stspace state' 255 patbyte bordcur arr t
          Just arr''     := arr'
            | Nothing =>
                Nothing # t
       in assert_total (go stspace (S state) arr'' bord t)
