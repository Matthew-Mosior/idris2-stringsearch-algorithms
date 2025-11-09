||| Fast Knuth-Morris-Pratt search of ByteStrings
module Data.ByteString.Search.KnuthMorrisPratt

import Data.Array.Core
import Data.Array.Mutable
import Data.Bits
import Data.ByteString
import Data.Linear.Ref1
import Data.So

%hide Data.Buffer.Core.get
%hide Data.Buffer.Core.set

%default total

||| Returns list of match starting positions of a pattern
||| (0-based) across the list of `ByteStrings`.
private
matcher :  Bool
        -> ByteString
        -> List ByteString
        -> F1 s (List Nat)
matcher overlap pat chunks t =
  case null pat of
    True  =>
      let chunks' # t := go Z chunks t
        in Z :: chunks # t
    False =>
      let bords # t := kmpBorders pat t
        in searcher Z Z pat chunks bords overlap t
  where
    mutual
      go :  Nat
         -> List ByteString
         -> F1 s (List ByteString)
      go _     []     t =
        [] # t
      go prior (s:ss) t =
        let l      := length s
            prior' := plus prior l
            s'     := [ prior' | i <- [1..l]]
          in s' ++ go prior' ss t
      findMatch :  (pati : Nat)
                -> (stri : Nat)
                -> (pat : ByteString)
                -> (strs : List ByteString)
                -> (bords : MArray s (S (length pat)) Nat)
                -> (overlap : Bool)
                -> F1 s (List Nat)
      findMatch pati stri pat strs@(str::rest) bords overlap t =
        let patlen := length pat
          in case pati == patlen of
               True  =>
                 case overlap of
               False =>
                 let strlen := length str
                   in case stri == strlen of
                        True  =>
                          assert_total (searcher (plus prior strlen) pati pat rest bords t)
                        False =>
                          let pati' := index pati pat
                            in case pati' of
                                 Nothing     =>
                                   (assert_total $ idris_crash "Data.ByteString.Search.KnuthMorrisPratt.matcher.findMatch: can't index into ByteString") # t
                                 Just pati'' =>
                                   let stri' := index stri str
                                     in case stri' of
                                          Nothing     =>
                                            (assert_total $ idris_crash "Data.ByteString.Search.KnuthMorrisPratt.matcher.findMatch: can't index into ByteString") # t
                                          Just stri'' =>
                                            case stri'' == pati'' of
                                              True  =>
                                                findMatch (S pati) (S stri) pat str t
                                              False =>
                                                case tryNatToFin pati of
                                                  Nothing      =>
                                                    (assert_total $ idris_crash "Data.ByteString.Search.KnuthMorrisPratt.matcher.findMatch: can't convert Nat to Fin") # t        
                                                  Just pati''' =>
                                                    let pati'''' # t := get bords pati''' t
                                                      in case pati'''' == Z of
                                                           True  =>
                                                             assert_total (checkHead (S stri) pat str bords t)
                                                           False =>
                                                             assert_total (findMatch pati'''' stri pat str bords t)
      checkHead :  (stri : Nat)
                -> (pat : ByteString)
                -> (str : ByteString)
                -> (bords : MArray s (S (length pat)) Nat)
                -> (overlap : Bool)
                -> F1 s (List Nat)
      checkHead stri pat str bords overlap t =
        let strlen := length str
          in case stri == strlen of
               True  =>
               False =>
                 let stri' := index stri str
                   in case stri' of
                        Nothing     =>
                          (assert_total $ idris_crash "Data.ByteString.Search.KnuthMorrisPratt.matcher.checkHead: can't index into ByteString") # t
                        Just stri'' =>
                          let patzero := index Z pat
                            in case patzero of
                                 Nothing       =>
                                   (assert_total $ idris_crash "Data.ByteString.Search.KnuthMorrisPratt.matcher.checkHead: can't index into ByteString") # t
                                 Just patzero' =>
                                   case stri'' == patzero' of
                                     True  =>
                                       findMatch (S Z) (S stri) pat str bords overlap t
                                     False =>
                                       assert_total (checkHead (S stri) pat str bords overlap t)
      searcher :  (prior : Nat)
               -> (patpos : Nat)
               -> (pat : ByteString)
               -> (strs : List ByteString)
               -> (bords : MArray s (S (length pat)) Nat)
               -> (overlap : Bool)
               -> F1 s (List Nat)
      searcher _     _      _   []            _     _       t =
        [] # t
      searcher _     Z      pat strs@(str::_) bords overlap t =
        checkHead Z pat str bords overlap t
      searcher prior patpos pat strs          bords overlap t =
        findMatch patpos Z pat strs bords overlap t
