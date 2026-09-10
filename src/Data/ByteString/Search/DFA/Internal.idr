||| Utilities for the DFA string searching algorithm.
module Data.ByteString.Search.DFA.Internal

import Data.Array.Core
import Data.Bits
import Data.ByteString
import Data.ByteString.Search.Internal.Utils
import Data.DArray
import Data.Enum
import Data.Linear.Ref1

%hide Data.Buffer.Core.get
%hide Data.Buffer.Core.set
%hide Data.List.Elem.get

%default total

||| One greater than the maximum number of DFA states whose flattened
||| 256-way transition table can be represented without overflow in
||| `Bits32`.
|||
||| A DFA must have fewer than 2^24 states because every state owns 256
||| transition entries:
|||
|||     states * 256 < 2^32
|||
public export
dfaStateLimit : Bits32
dfaStateLimit = 0x01000000

||| Evidence that a DFA state count can safely be used to construct a
||| flattened 256-way transition table using `Bits32` indexing.
|||
||| The proof stored by `Index` is erased at runtime.
|||
public export
DFAStateCount : Type
DFAStateCount = Index dfaStateLimit

||| A valid state in a DFA containing `states` states.
|||
||| The underlying state number is represented by `Index`, so its proof that
||| the state lies in `[0, states)` is erased at runtime.
|||
public export
DFAState : Bits32 -> Type
DFAState = Index

||| A valid DFA transition coordinate.
|||
||| `state` is already known to be within the DFA's state range, while `byte`
||| is intrinsically limited to the 256 possible byte values.
|||
public export
record DFAIndex (states : Bits32) where
  constructor MkDFAIndex
  state : Index states
  byte  : Bits8

||| Proof that flattening a valid DFA state and input byte yields a valid
||| transition-table index.
|||
||| `statesPrf` guarantees that `states * 256` cannot overflow `Bits32`.
||| `statePrf` guarantees that `state < states`, while a `Bits8` value is
||| intrinsically smaller than 256.
|||
||| This function and all of its proof arguments are erased at runtime.
|||
0 dfaIndexLT :  (state : Bits32)
             -> {states : Bits32}
             -> (0 statesPrf : states < Data.ByteString.Search.DFA.Internal.dfaStateLimit)
             -> (0 statePrf : state < states)
             -> (byte : Bits8)
             -> ((state * 256) + cast byte) < (states * 256)
dfaIndexLT state statesPrf statePrf byte =
  believe_me ()

||| Flatten a DFA state and input byte into a transition-table index.
|||
||| The resulting `Index` is constructed directly from statically carried
||| bounds evidence. No dynamic range check is performed.
|||
||| The DFA state-count proof guarantees that multiplication by 256 cannot
||| overflow `Bits32`.
|||
export %inline
dfaIndex :  {states : Bits32}
         -> {auto 0 statesPrf : states < Data.ByteString.Search.DFA.Internal.dfaStateLimit}
         -> DFAIndex states
         -> Index (states * 256)
dfaIndex (MkDFAIndex (I state {prf}) byte) =
  I ((state * 256) + cast byte) {prf = dfaIndexLT state statesPrf prf byte}

||| Return the runtime state number represented by a valid DFA state.
|||
||| The bound proof carried by `Index` is erased, so this operation is
||| simply extraction of the underlying `Bits32` value.
|||
export %inline
dfaStateValue : DFAState states -> Bits32
dfaStateValue (I state) = state

||| Construct the valid flattened transition-table index for a DFA state and
||| input byte.
|||
||| No dynamic bounds check is performed. The state-count bound and state
||| bound are carried exclusively as erased evidence.
|||
export %inline
dfaTransitionIndex :  {states : Bits32}
                   -> {auto 0 statesPrf : states < Data.ByteString.Search.DFA.Internal.dfaStateLimit}
                   -> DFAState states
                   -> Bits8
                   -> Index (states * 256)
dfaTransitionIndex state byte =
  dfaIndex (MkDFAIndex state byte)

||| Mutable DFA transition storage.
|||
||| The underlying pointer is an Idris primitive array containing
||| `states * 256` transitions.
|||
public export
record DFATable (s : Type) (states : Bits32) where
  constructor MkDFATable
  arr : AnyPtr

||| Allocate an uninitialized DFA transition table.
|||
export
newDFATable :  {states : Bits32}
            -> {auto 0 statesPrf : states < Data.ByteString.Search.DFA.Internal.dfaStateLimit}
            -> F1 s (DFATable s states)
newDFATable {states} t =
  let arr # t := ffi (prim__emptyArray $ cast (states * 256)) t
    in MkDFATable arr # t

||| Read the next DFA state for a current state and input byte.
|||
||| The flattened transition index is already bounded, so no explicit
||| `tryIndex` or `tryNatToFin` conversion occurs in the search loop.
|||
||| The primitive array is accessed directly using the prevalidated
||| flattened `Index`.
|||
export %inline
dfaTransition :  {states : Bits32}
              -> {auto 0 statesPrf : states < Data.ByteString.Search.DFA.Internal.dfaStateLimit}
              -> DFATable s states
              -> DFAState states
              -> Bits8
              -> F1 s (DFAState states)
dfaTransition table state byte t =
  let I index = dfaTransitionIndex state byte
    in believe_me (prim__arrayGet table.arr (cast index)) # t

||| Write a DFA transition.
|||
||| The flattened index is derived from an already-bounded DFA state and
||| byte, avoiding any explicit dynamic bounds conversion.
|||
||| The primitive array is written directly using the prevalidated
||| flattened `Index`.
|||
export %inline
setDFATransition :  {states : Bits32}
                 -> {auto 0 statesPrf : states < Data.ByteString.Search.DFA.Internal.dfaStateLimit}
                 -> DFATable s states
                 -> DFAState states
                 -> Bits8
                 -> DFAState states
                 -> F1' s
setDFATransition table state byte next =
  let I index = dfaTransitionIndex state byte
    in ffi (prim__arraySet table.arr (cast index) (believe_me next))

||| Runtime description of a valid DFA state space.
|||
||| `states` is the number of states in the DFA. The erased proofs establish
||| that the state count is positive and small enough for the flattened
||| 256-way transition table to fit within the `Bits32` index space.
|||
public export
record DFAStateSpace where
  constructor MkDFAStateSpace
  states : Bits32
  0 statesPositive : 0 < states
  0 statesBounded : states < Data.ByteString.Search.DFA.Internal.dfaStateLimit

||| Construct the state space for a DFA matching `bs`.
|||
||| A pattern of length `n` requires `n + 1` states, including state zero.
||| The upper-bound check is performed once during DFA construction. All
||| subsequent state and transition indexing carries erased `Index` proofs
||| and requires no repeated bounds validation.
|||
export
dfaStateSpace : ByteString -> Maybe DFAStateSpace
dfaStateSpace bs =
  let states : Bits32
      states = cast $ S (length bs)
    in case tryIndex {r = dfaStateLimit} states of
         Nothing                =>
           Nothing
         Just (I states' {prf}) =>
           Just (MkDFAStateSpace states' (believe_me ()) prf)

||| A constructed DFA transition automaton.
|||
||| The runtime state-space description is packaged together with a
||| transition table indexed by that state count.
|||
||| Every transition stored in the table is itself a valid `DFAState`,
||| allowing a lookup result to feed directly into the next lookup.
|||
public export
record DFAutomaton (s : Type) where
  constructor MkDFAutomaton
  space : DFAStateSpace
  table : DFATable s space.states

||| Convert a `Nat` state number into a valid state of the supplied DFA
||| state space.
|||
||| This helper is used only while constructing the DFA. Search-time
||| transitions already produce bounded states directly and therefore do not
||| require this check.
|||
private
toDFAState :  (space : DFAStateSpace)
           -> Nat
           -> Maybe (DFAState space.states)
toDFAState space n =
  tryIndex {r = space.states} (cast n)

||| State zero for a valid DFA state space.
|||
||| No dynamic check is required because every DFA state space is known to
||| contain at least one state.
|||
private
zeroDFAState :  (space : DFAStateSpace)
             -> DFAState space.states
zeroDFAState space =
  I 0 {prf = space.statesPositive}

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
||| The KMP border table is currently retained in its existing `MArray`
||| representation; it is used only during automaton construction and will be
||| migrated separately.
|||
export
automaton :
     (bs : ByteString)
  -> F1 s (Maybe (DFAutomaton s))
automaton bs t =
  let Just space = dfaStateSpace bs
        | Nothing =>
            Nothing # t

      arr # t =
        newDFATable
          {states = space.states}
          {statesPrf = space.statesBounded}
          t

      bord # t =
        kmpBorders bs t

      Just bord' = bord
        | Nothing =>
            Nothing # t

      arr' # t =
        go space Z arr bord' t

      Just arr'' = arr'
        | Nothing =>
            Nothing # t

   in Just (MkDFAutomaton space arr'') # t

  where
    fillState :
         (space : DFAStateSpace)
      -> (state : DFAState space.states)
      -> (byte : Bits8)
      -> (patbyte : Maybe Bits8)
      -> (bordcur : DFAState space.states)
      -> (arr : DFATable s space.states)
      -> F1 s (Maybe (DFATable s space.states))
    fillState space state byte patbyte bordcur arr t =
      let stateval = dfaStateValue state

          Just patbyte' = patbyte
            | Nothing =>
                let False = stateval == 0
                      | True =>
                          let zero =
                                zeroDFAState space

                              () # t =
                                setDFATransition
                                  {statesPrf = space.statesBounded}
                                  arr
                                  state
                                  byte
                                  zero
                                  t

                              True = byte == 0
                                | False =>
                                    assert_total $
                                      fillState
                                        space
                                        state
                                        (byte - 1)
                                        patbyte
                                        bordcur
                                        arr
                                        t

                           in Just arr # t

                    bordcur' # t =
                      dfaTransition
                        {statesPrf = space.statesBounded}
                        arr
                        bordcur
                        byte
                        t

                    () # t =
                      setDFATransition
                        {statesPrf = space.statesBounded}
                        arr
                        state
                        byte
                        bordcur'
                        t

                    True = byte == 0
                      | False =>
                          assert_total $
                            fillState
                              space
                              state
                              (byte - 1)
                              patbyte
                              bordcur'
                              arr
                              t

                 in Just arr # t

          False = byte == patbyte'
            | True =>
                let Just next =
                      toDFAState space (S $ cast stateval)
                      | Nothing =>
                          Nothing # t

                    () # t =
                      setDFATransition
                        {statesPrf = space.statesBounded}
                        arr
                        state
                        byte
                        next
                        t

                    True = byte == 0
                      | False =>
                          assert_total $
                            fillState
                              space
                              state
                              (byte - 1)
                              patbyte
                              bordcur
                              arr
                              t

                 in Just arr # t

          False = stateval == 0
            | True =>
                let zero =
                      zeroDFAState space

                    () # t =
                      setDFATransition
                        {statesPrf = space.statesBounded}
                        arr
                        state
                        byte
                        zero
                        t

                    True = byte == 0
                      | False =>
                          assert_total $
                            fillState
                              space
                              state
                              (byte - 1)
                              patbyte
                              bordcur
                              arr
                              t

                 in Just arr # t

          bordcur' # t =
            dfaTransition
              {statesPrf = space.statesBounded}
              arr
              bordcur
              byte
              t

          () # t =
            setDFATransition
              {statesPrf = space.statesBounded}
              arr
              state
              byte
              bordcur'
              t

          True = byte == 0
            | False =>
                assert_total $
                  fillState
                    space
                    state
                    (byte - 1)
                    patbyte
                    bordcur'
                    arr
                    t

       in Just arr # t

    go :
         (space : DFAStateSpace)
      -> (state : Nat)
      -> (arr : DFATable s space.states)
      -> (bord : MArray s (S (length bs)) Nat)
      -> F1 s (Maybe (DFATable s space.states))
    go space state arr bord t =
      let False = state > length bs
            | True =>
                Just arr # t

          Just state' =
            toDFAState space state
            | Nothing =>
                Nothing # t

          Just bordidx =
            tryNatToFin state
            | Nothing =>
                Nothing # t

          bordcurNat # t =
            get bord bordidx t

          Just bordcur =
            toDFAState space bordcurNat
            | Nothing =>
                Nothing # t

          patbyte =
            index state bs

          arr' # t =
            fillState
              space
              state'
              255
              patbyte
              bordcur
              arr
              t

          Just arr'' = arr'
            | Nothing =>
                Nothing # t

       in assert_total $
            go
              space
              (S state)
              arr''
              bord
              t
