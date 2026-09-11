||| Utilities for the Boyer-Moore string searching algorithm.
module Data.ByteString.Search.BoyerMoore.Internal

import Data.Array.Core
import Data.Bits
import Data.ByteString
import Data.Enum
import Data.Linear.Ref1

%hide Data.Buffer.Core.get
%hide Data.Buffer.Core.set
%hide Data.List.Elem.get

%default total

||| One greater than the maximum supported Boyer–Moore pattern size.
|||
||| Pattern-table indices are represented by `Bits32`, so the pattern length
||| must fit within that index space.
public export
bmPatternLimit : Bits32
bmPatternLimit = 0xffffffff

||| Runtime description of a Boyer–Moore pattern index space.
|||
||| `size` is the number of bytes in the pattern. Boyer–Moore preprocessing
||| requires a nonempty pattern, so every valid pattern space contains at
||| least one index.
|||
public export
record BMPatternSpace where
  constructor MkBMPatternSpace
  size : Bits32
  0 sizePositive : 0 < size
  0 sizeBounded : size < Data.ByteString.Search.BoyerMoore.Internal.bmPatternLimit

||| A valid position within a Boyer–Moore pattern.
|||
||| The bound proof carried by `Index` is erased at runtime.
|||
public export
PatternIndex : Bits32 -> Type
PatternIndex = Index

||| Construct the Boyer–Moore index space for a nonempty pattern.
|||
||| The pattern size is validated once during preprocessing. Subsequent table
||| accesses use bounded `PatternIndex` values.
|||
export
bmPatternSpace :  (bs : ByteString)
               -> {0 prf : So (not $ null bs)}
               -> Maybe BMPatternSpace
bmPatternSpace bs =
  let size : Bits32
      size = cast $ length bs
   in case tryIndex {r = bmPatternLimit} size of
        Nothing              =>
          Nothing
        Just (I size' {prf = sizePrf}) =>
          Just (MkBMPatternSpace size' (believe_me ()) sizePrf)

||| Return the runtime value represented by a bounded pattern index.
|||
export %inline
patternIndexValue :  {size : Bits32}
                  -> PatternIndex size
                  -> Bits32
patternIndexValue (I idx) = idx

||| Convert a construction-time `Nat` position into a bounded pattern index.
|||
||| This validation is used during preprocessing and is not part of the
||| Boyer–Moore target-scanning hot path.
|||
export %inline
toPatternIndex :  (space : BMPatternSpace)
               -> Nat
               -> Maybe (PatternIndex space.size)
toPatternIndex space idx =
  tryIndex {r = space.size} (cast idx)

||| Runtime-sized mutable integer table used by Boyer–Moore preprocessing.
|||
||| The underlying primitive array contains exactly `size` entries.
|||
public export
record BMIntTable (s : Type) (size : Bits32) where
  constructor MkBMIntTable
  arr : AnyPtr

||| A runtime-sized Boyer–Moore integer table packaged with its pattern
||| index space.
|||
public export
record BMPatternTable (s : Type) where
  constructor MkBMPatternTable
  space : BMPatternSpace
  table : BMIntTable s space.size

||| Allocate an uninitialized Boyer–Moore integer table.
|||
export
newBMIntTable :  {size : Bits32}
              -> F1 s (BMIntTable s size)
newBMIntTable {size} t =
  let arr # t := ffi (prim__emptyArray $ cast size) t
   in MkBMIntTable arr # t

||| Read an entry from a Boyer–Moore integer table.
|||
||| The index is already bounded, so no dynamic table-bounds conversion is
||| performed.
|||
export %inline
bmGet :  {size : Bits32}
      -> BMIntTable s size
      -> PatternIndex size
      -> F1 s Int
bmGet table idx t =
  let I pos := idx
   in believe_me (prim__arrayGet table.arr (cast pos)) # t

||| Write an entry to a Boyer–Moore integer table.
|||
||| The index is already bounded, so no dynamic table-bounds conversion is
||| performed.
|||
export %inline
bmSet :  {size : Bits32}
      -> BMIntTable s size
      -> PatternIndex size
      -> Int
      -> F1' s
bmSet table idx value t =
  let I pos := idx
   in ffi (prim__arraySet table.arr (cast pos) (believe_me value)) t

||| Allocate and initialize every entry in a Boyer–Moore integer table.
|||
||| The initialization loop ranges from zero to `size - 1`, so each primitive
||| write is known by construction to lie within the newly allocated array.
|||
export
newBMIntTableWith :  {size : Bits32}
                  -> Int
                  -> F1 s (BMIntTable s size)
newBMIntTableWith {size} initial t =
  let table # t := newBMIntTable {size} t
    in fill 0 table t
  where
    fill :  {size : Bits32}
         -> Bits32
         -> BMIntTable s size
         -> F1 s (BMIntTable s size)
    fill idx table t =
      let False  := idx == size
            | True =>
                table # t
          () # t := ffi (prim__arraySet table.arr (cast idx) (believe_me initial)) t
        in assert_total (fill (idx + 1) table t)

||| Mutable Boyer–Moore bad-character occurrence table.
|||
||| The table contains exactly one entry for each possible byte value and can
||| therefore be indexed directly by `Bits8`.
|||
public export
record OccurrenceTable (s : Type) where
  constructor MkOccurrenceTable
  arr : AnyPtr

||| Allocate an occurrence table with every byte initialized to shift `1`.
|||
export
newOccurrenceTable : F1 s (OccurrenceTable s)
newOccurrenceTable t =
  let arr # t := ffi (prim__emptyArray 256) t
      table   := MkOccurrenceTable arr
   in fill 0 table t
  where
    fill :  Nat
         -> OccurrenceTable s
         -> F1 s (OccurrenceTable s)
    fill idx table t =
      let False := idx == 256
            | True =>
                table # t
          () # t := ffi (prim__arraySet table.arr (cast idx) (believe_me $ the Int 1)) t
       in assert_total (fill (S idx) table t)

||| Read the bad-character entry associated with a byte.
|||
||| Since `Bits8` intrinsically ranges from 0 through 255, no bounds
||| conversion or validation is required.
|||
export %inline
occurrence :  OccurrenceTable s
           -> Bits8
           -> F1 s Int
occurrence table byte t =
  believe_me (prim__arrayGet table.arr (cast byte)) # t

||| Write the bad-character entry associated with a byte.
|||
||| Since `Bits8` intrinsically ranges from 0 through 255, no bounds
||| conversion or validation is required.
|||
export %inline
setOccurrence :  OccurrenceTable s
              -> Bits8
              -> Int
              -> F1' s
setOccurrence table byte value t =
  ffi (prim__arraySet table.arr (cast byte) (believe_me value)) t

||| Constructs a lookup table recording the last occurrence of each byte
||| in the given pattern.
|||
||| For every byte value, the table stores the negated index of its last
||| occurrence within the pattern, excluding the final pattern position.
|||
||| The table is indexed directly by `Bits8`, eliminating the previous
||| `Bits8 -> Nat -> Fin 256` conversion and its dynamic bounds validation.
|||
||| O((length of pattern) + 256)
|||
export
occurrences :  (bs : ByteString)
            -> {0 prf : So (not $ null bs)}
            -> F1 s (Maybe (OccurrenceTable s))
occurrences bs t =
  let arr # t := newOccurrenceTable t
    in go Z (length bs) arr t
  where
    go :  (i : Nat)
      -> (patend : Nat)
      -> OccurrenceTable s
      -> F1 s (Maybe (OccurrenceTable s))
    go i patend arr t =
      let False     := S i >= patend
            | True =>
                Just arr # t
          Just byte := index i bs
            | Nothing =>
                Nothing # t
          ()    # t := setOccurrence arr byte (negate $ cast {to=Int} i) t
       in assert_total (go (S i) patend arr t)

||| Builds the table of suffix lengths for the given pattern.
|||
||| The table is backed by a runtime-sized primitive array containing exactly
||| `length bs` entries.
|||
||| Table positions are represented by bounded `PatternIndex` values rather
||| than `Fin (length bs)`, eliminating `tryNatToFin` from primitive table
||| reads and writes.
|||
export
suffixLengths :  (bs : ByteString)
              -> {0 prf : So (not $ null bs)}
              -> F1 s (Maybe (BMPatternTable s))
suffixLengths bs {prf} t =
  let Just stspace := bmPatternSpace bs {prf = prf}
        | Nothing =>
            Nothing # t
      arr      # t := newBMIntTableWith {size = stspace.size} 0 t
      lastidxnat   := minus (length bs) 1
      Just lastidx := toPatternIndex stspace lastidxnat
        | Nothing =>
            Nothing # t
      ()       # t := bmSet arr lastidx (cast {to=Int} $ length bs) t
      arr'     # t := noSuffix stspace (cast {to=Int} $ minus (length bs) 2) arr t
      Just arr''   := arr'
        | Nothing =>
            Nothing # t
    in Just (MkBMPatternTable stspace arr'') # t
  where
    dec :  (diff : Int)
        -> (j : Int)
        -> F1 s (Maybe Int)
    dec diff j t =
      let False        := j < 0
            | True =>
                Just j # t
          Just jbyte   := index (cast {to=Nat} j) bs
            | Nothing =>
                Nothing # t
          Just shifted := index (cast {to=Nat} (j + diff)) bs
            | Nothing =>
                Nothing # t
          False        := jbyte /= shifted
            | True =>
                Just j # t
        in assert_total (dec diff (j - 1) t)
    mutual
      suffixLoop :  (stspace : BMPatternSpace)
                 -> (pre : Int)
                 -> (end : Int)
                 -> (idx : Int)
                 -> (arr : BMIntTable s stspace.size)
                 -> F1 s (Maybe (BMIntTable s stspace.size))
      suffixLoop _       _   _   0   arr t =
        Just arr # t
      suffixLoop stspace pre end idx arr t =
        let True         := pre < idx
              | False =>
                  noSuffix stspace idx arr t
            Just idxbyte := index (cast {to=Nat} idx) bs
              | Nothing =>
                  Nothing # t
            Just endbyte := index (minus (length bs) 1) bs
              | Nothing =>
                  Nothing # t
            Just idxpos := toPatternIndex stspace (cast {to=Nat} idx)
              | Nothing =>
                  Nothing # t
            False       := idxbyte /= endbyte
              | True =>
                  let () # t := bmSet arr idxpos 0 t
                    in assert_total (suffixLoop stspace pre (end - 1) (idx - 1) arr t)
            Just endpos := toPatternIndex stspace (cast {to=Nat} end)
              | Nothing =>
                  Nothing # t
            prevs   # t := bmGet arr endpos t
            False       := (pre + prevs) < idx
              | True =>
                  let () # t := bmSet arr idxpos prevs t
                    in assert_total (suffixLoop stspace pre (end - 1) (idx - 1) arr t)
            pri     # t := dec (cast {to=Int} (minus (length bs) (cast {to=Nat} idx))) pre t
            Just pri'   := pri
              | Nothing =>
                  Nothing # t
            ()      # t := bmSet arr idxpos (idx - pri') t
          in assert_total (suffixLoop stspace pri' (cast {to=Int} $ minus (length bs) 2) (idx - 1) arr t)
      noSuffix :  (stspace : BMPatternSpace)
               -> (i : Int)
               -> (arr : BMIntTable s stspace.size)
               -> F1 s (Maybe (BMIntTable s stspace.size))
      noSuffix _       0 arr t =
        Just arr # t
      noSuffix stspace i arr t =
        let Just patati   := index (cast {to=Nat} i) bs
              | Nothing =>
                  Nothing # t
            Just patatend := index (minus (length bs) 1) bs
              | Nothing =>
                  Nothing # t
            Just ipos     := toPatternIndex stspace (cast {to=Nat} i)
              | Nothing =>
                  Nothing # t
            True          := patati == patatend
              | False =>
                  let () # t := bmSet arr ipos 0 t
                    in assert_total (noSuffix stspace (i - 1) arr t)
            diff             := cast {to=Int} (minus (length bs) 1) - i
            nexti            := i - 1
            previ        # t := dec diff nexti t
            Just previ'      := previ
              | Nothing =>
                  Nothing # t
            False            := previ' == nexti
              | True =>
                  let () # t := bmSet arr ipos 1 t
                    in assert_total (noSuffix stspace nexti arr t)
            ()           # t := bmSet arr ipos (i - previ') t
          in assert_total (suffixLoop stspace previ' (cast {to=Int} $ minus (length bs) 2) nexti arr t)

||| Build the Boyer–Moore good-suffix shift table.
|||
||| The suffix-length table and resulting shift table share the same bounded
||| pattern index space.
|||
||| Primitive table accesses therefore use `PatternIndex` rather than
||| dynamically constructed `Fin` values.
|||
export
suffixShifts :  (bs : ByteString)
             -> {0 prf : So (not $ null bs)}
             -> F1 s (Maybe (BMPatternTable s))
suffixShifts bs {prf} t =
  let suff                              # t := suffixLengths bs {prf = prf} t
      Just (MkBMPatternTable stspace suff') := suff
        | Nothing =>
            Nothing # t
      arr                               # t := newBMIntTableWith {size = stspace.size} (cast {to=Int} $ length bs) t
      arr'                              # t := prefixShift stspace (cast {to=Int} $ minus (length bs) 2) 0 suff' arr t
      Just arr''                            := arr'
        | Nothing =>
            Nothing # t
      arr'''                            # t := suffixShift stspace 0 suff' arr'' t
      Just arr''''                          := arr'''
        | Nothing =>
            Nothing # t
    in Just (MkBMPatternTable stspace arr'''') # t
  where
    fillToShift :  (stspace : BMPatternSpace)
                -> (i : Int)
                -> (shift : Int)
                -> (arr : BMIntTable s stspace.size)
                -> F1 s (Maybe (BMIntTable s stspace.size))
    fillToShift stspace i shift arr t =
      let False     := i == shift
            | True =>
                Just arr # t
          Just ipos := toPatternIndex stspace (cast {to=Nat} i)
            | Nothing =>
                Nothing # t
          ()    # t := bmSet arr ipos shift t
        in assert_total (fillToShift stspace (i + 1) shift arr t)
    prefixShift :  (stspace : BMPatternSpace)
                -> (idx : Int)
                -> (j : Int)
                -> (suff : BMIntTable s stspace.size)
                -> (arr : BMIntTable s stspace.size)
                -> F1 s (Maybe (BMIntTable s stspace.size))
    prefixShift stspace idx j suff arr t =
      let False       := idx < 0
            | True =>
                Just arr # t
          Just idxpos := toPatternIndex stspace (cast {to=Nat} idx)
            | Nothing =>
                Nothing # t
          idxval  # t := bmGet suff idxpos t
          True        := idxval == idx + 1
            | False =>
                assert_total (prefixShift stspace (idx - 1) j suff arr t)
          shift       := cast {to=Int} (minus (length bs) 1) - idx
          arr'    # t := fillToShift stspace j shift arr t
          Just arr''  := arr'
            | Nothing =>
                Nothing # t
        in assert_total (prefixShift stspace (idx - 1) shift suff arr'' t)
    suffixShift :  (stspace : BMPatternSpace)
                -> (idx : Int)
                -> (suff : BMIntTable s stspace.size)
                -> (arr : BMIntTable s stspace.size)
                -> F1 s (Maybe (BMIntTable s stspace.size))
    suffixShift stspace idx suff arr t =
      let patend         := cast {to=Int} (minus (length bs) 1)
          False          := idx >= patend
            | True =>
                Just arr # t
          Just idxpos    := toPatternIndex stspace (cast {to=Nat} idx)
            | Nothing =>
                Nothing # t
          sufflen    # t := bmGet suff idxpos t
          target         := patend - sufflen
          Just targetpos := toPatternIndex stspace (cast {to=Nat} target)
            | Nothing =>
                Nothing # t
          value          := patend - idx
          ()         # t := bmSet arr targetpos value t
        in assert_total (suffixShift stspace (idx + 1) suff arr t)
