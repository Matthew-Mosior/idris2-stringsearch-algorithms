||| Utilities for the Knuth-Morris-Pratt string searching algorithm.
module Data.ByteString.Search.KnuthMorrisPratt.Internal

import Data.Array.Core
import Data.Bits
import Data.ByteString
import Data.ByteString.Search.DFA.Types
import Data.DArray
import Data.Enum
import Data.Linear.Ref1

%hide Data.Buffer.Core.get
%hide Data.Buffer.Core.set
%hide Data.ByteString.Search.DFA.Types.DFAStateSpace.states
%hide Data.List.Elem.get

%default total

||| Mutable storage for the KMP border table.
|||
||| The table contains one entry for every DFA state. Both table indices and
||| stored border values are represented by `DFAState`, so their bounds are
||| established once and carried as erased evidence.
|||
||| The underlying storage is an Idris primitive array.
|||
public export
record KMPBorderTable (s : Type) (states : Bits32) where
  constructor MkKMPBorderTable
  arr : AnyPtr

||| A constructed KMP border table together with the DFA state space to
||| which its indices and values belong.
|||
||| Packaging the state space with the table allows `automaton` to reuse the
||| exact same state-space witness rather than independently reconstructing
||| and validating the pattern's state count.
|||
public export
record KMPBorders (s : Type) where
  constructor MkKMPBorders
  space : DFAStateSpace
  table : KMPBorderTable s space.states

||| Allocate an uninitialized KMP border table.
|||
||| The table contains exactly one entry for each DFA state.
|||
export
newKMPBorderTable :  {states : Bits32}
                  -> F1 s (KMPBorderTable s states)
newKMPBorderTable {states} t =
  let arr # t := ffi (prim__emptyArray $ cast states) t
    in MkKMPBorderTable arr # t

||| Read a border value from the KMP border table.
|||
||| The supplied index is already a valid `DFAState`, so no dynamic bounds
||| validation is required. The stored result is itself another valid DFA
||| state.
|||
export %inline
kmpBorder :  KMPBorderTable s states
          -> DFAState states
          -> F1 s (DFAState states)
kmpBorder table state t =
  let I idx := state
   in believe_me (prim__arrayGet table.arr (cast idx)) # t

||| Write a border value to the KMP border table.
|||
||| Both the destination index and stored border value are already bounded by
||| the same DFA state space, so no `Fin` conversion or runtime bounds check
||| is required.
|||
export %inline
setKMPBorder :  KMPBorderTable s states
             -> DFAState states
             -> DFAState states
             -> F1' s
setKMPBorder table state border t =
  let I idx := state
   in ffi (prim__arraySet table.arr (cast idx) (believe_me border)) t

||| Construct the successor of a DFA state during DFA preprocessing.
|||
||| This check occurs only while constructing preprocessing tables. It is
||| never executed by the target-scanning DFA hot path.
|||
export %inline
nextDFAState :  (space : DFAStateSpace)
             -> DFAState space.states
             -> Maybe (DFAState space.states)
nextDFAState space state =
  tryIndex {r = space.states} (dfaStateValue state + 1)

||| Computes the suffix-oriented KMP border table for a given pattern.
|||
||| Each entry associated with DFA state `i` stores the length of the longest
||| proper prefix of `pattern[0..i-1]` that is also a suffix.
|||
||| Unlike the previous implementation, table indices and border values are
||| represented directly by bounded `DFAState` values rather than `Nat`
||| values indexed through `Fin`.
|||
||| Consequently, accesses to the border table require no `tryNatToFin` or
||| equivalent dynamic table-bounds conversion.
|||
||| The result packages the table together with its `DFAStateSpace`, allowing
||| construction of the DFA transition table to reuse exactly the same state
||| space.
|||
||| Example: "ANPANMAN"
|||
||| Indices:  0  1  2  3  4  5  6  7  8
||| Borders:  0  0  0  0  1  2  0  1  2
|||
export
kmpBorders :  (bs : ByteString)
           -> F1 s (Maybe (KMPBorders s))
kmpBorders bs t =
  let Just stspace := dfaStateSpace bs
        | Nothing =>
            Nothing # t
      arr # t      := newKMPBorderTable {states = stspace.states} t
      zero         : DFAState stspace.states
      zero         := I 0 {prf = stspace.statesPositive}
      ()       # t := setKMPBorder arr zero zero t
      Just one     := nextDFAState stspace zero
        | Nothing =>
            Nothing # t
    in go stspace one zero arr t
  where
    mutual
      ||| Continue resolving the border for the current pattern position.
      |||
      ||| On a matching pattern byte, both the current pattern position and
      ||| border position advance by one. On a mismatch, the previous border
      ||| value is read directly from the bounded KMP border table.
      |||
      advance :  (stspace : DFAStateSpace)
              -> (i : DFAState stspace.states)
              -> (j : DFAState stspace.states)
              -> (wi : Bits8)
              -> (arr : KMPBorderTable s stspace.states)
              -> F1 s (Maybe (KMPBorders s))
      advance stspace i j wi arr t =
        let jidx    := cast {to=Nat} (dfaStateValue j)
            Just wj := index jidx bs
              | Nothing =>
                  Nothing # t
            False   := wi == wj
              | True =>
                  let Just i' := nextDFAState stspace i
                        | Nothing =>
                            Nothing # t
                      Just j' := nextDFAState stspace j
                        | Nothing =>
                            Nothing # t
                      () # t := setKMPBorder arr i' j' t
                    in assert_total (go stspace i' j' arr t)
            False   := dfaStateValue j == 0
              | True =>
                  let Just i' := nextDFAState stspace i
                        | Nothing =>
                            Nothing # t
                      zero    : DFAState stspace.states
                      zero    := I 0 {prf = stspace.statesPositive}
                      ()  # t := setKMPBorder arr i' zero t
                    in assert_total (go stspace i' zero arr t)
            j'  # t := kmpBorder arr j t
          in assert_total (advance stspace i j' wi arr t)
      ||| Process the next pattern position while constructing the KMP border
      ||| table.
      |||
      ||| `i` and `j` are already valid DFA states, so border-table indexing
      ||| requires no dynamic conversion to `Fin`.
      |||
      go :  (stspace : DFAStateSpace)
         -> (i : DFAState stspace.states)
         -> (j : DFAState stspace.states)
         -> (arr : KMPBorderTable s stspace.states)
         -> F1 s (Maybe (KMPBorders s))
      go stspace i j arr t =
        let iidx    := cast {to=Nat} (dfaStateValue i)
            False   := iidx == length bs
              | True =>
                  Just (MkKMPBorders stspace arr) # t
            Just wi := index iidx bs
              | Nothing =>
                  Nothing # t
         in assert_total (advance stspace i j wi arr t)
