module Main

import BoyerMoore
import DFA
import KnuthMorrisPratt

import Data.ByteString.Search.BoyerMoore
import Data.ByteString.Search.DFA
import Data.ByteString.Search.KnuthMorrisPratt

import Data.Array
import Data.ByteString
import Data.Linear.Ref1
import Data.Linear.Token
import Data.So
import Profile

%hide Data.Linear.id
%hide Data.Linear.(::)
%hide Data.Vect.(::)
%hide Prelude.Stream.(::)

match_favoredBM : IO ()
match_favoredBM =
  case decSo $ (not $ null bmfavoredpat) of
    No  _      =>
      assert_total $ idris_crash "pat is null"
    Yes patprf =>
      case decSo $ (not $ null bmfavoredtarget) of
        No  _         =>
          assert_total $ idris_crash "target is null"
        Yes targetprf =>
          case decSo $ (length bmfavoredtarget) >= (length bmfavoredpat) of
            No  _         =>
              assert_total $ idris_crash "the target is shorter than the pattern"
            Yes lengthprf => do
              _ <-
                ( runIO $ \t =>
                    matchBM bmfavoredpat bmfavoredtarget {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t)
              pure ()

match_pathologicalBM : IO ()
match_pathologicalBM =
  case decSo $ (not $ null bmpathologicalpat) of
    No  _      =>
      assert_total $ idris_crash "pat is null"
    Yes patprf =>
      case decSo $ (not $ null bmpathologicaltarget) of
        No  _         =>
          assert_total $ idris_crash "target is null"
        Yes targetprf =>
          case decSo $ (length bmpathologicaltarget) >= (length bmpathologicalpat) of
            No  _         =>
              assert_total $ idris_crash "the target is shorter than the pattern"
            Yes lengthprf => do
              _ <-
                ( runIO $ \t =>
                    matchBM bmpathologicalpat bmpathologicaltarget {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t)
              pure ()

match_DFA : IO ()
match_DFA =
  case decSo $ (not $ null dfapat) of
    No  _      =>
      assert_total $ idris_crash "pat is null"
    Yes patprf =>
      case decSo $ (not $ null dfatarget) of
        No  _         =>
          assert_total $ idris_crash "target is null"
        Yes targetprf => do
          _ <-
            ( runIO $ \t =>
                matchDFA dfapat dfatarget {prfpat=patprf} {prftarget=targetprf} t)
          pure ()

match_favoredKMP : IO ()
match_favoredKMP =
  case decSo $ (not $ null kmpfavoredpat) of
    No  _      =>
      assert_total $ idris_crash "pat is null"
    Yes patprf =>
      case decSo $ (not $ null kmpfavoredtarget) of
        No  _         =>
          assert_total $ idris_crash "target is null"
        Yes targetprf => do
          _ <-
            ( runIO $ \t =>
                matchKMP kmpfavoredpat kmpfavoredtarget {prfpat=patprf} {prftarget=targetprf} t)
          pure ()

match_pathologicalKMP : IO ()
match_pathologicalKMP =
  case decSo $ (not $ null kmppathologicalpat) of
    No  _      =>
      assert_total $ idris_crash "pat is null"
    Yes patprf =>
      case decSo $ (not $ null kmppathologicaltarget) of
        No  _         =>
          assert_total $ idris_crash "target is null"
        Yes targetprf => do
          _ <-
            ( runIO $ \t =>
                matchKMP kmppathologicalpat kmppathologicaltarget {prfpat=patprf} {prftarget=targetprf} t)
          pure ()

indices_favoredBM : IO ()
indices_favoredBM =
  case decSo $ (not $ null bmfavoredpat) of
    No  _      =>
      assert_total $ idris_crash "pat is null"
    Yes patprf =>
      case decSo $ (not $ null bmfavoredtarget) of
        No  _         =>
          assert_total $ idris_crash "target is null"
        Yes targetprf =>
          case decSo $ (length bmfavoredtarget) >= (length bmfavoredpat) of
            No  _         =>
              assert_total $ idris_crash "the target is shorter than the pattern"
            Yes lengthprf => do
              _ <-
                ( runIO $ \t =>
                    indicesBM bmfavoredpat bmfavoredtarget {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t)
              pure ()

indices_pathologicalBM : IO ()
indices_pathologicalBM =
  case decSo $ (not $ null bmpathologicalpat) of
    No  _      =>
      assert_total $ idris_crash "pat is null"
    Yes patprf =>
      case decSo $ (not $ null bmpathologicaltarget) of
        No  _         =>
          assert_total $ idris_crash "target is null"
        Yes targetprf =>
          case decSo $ (length bmpathologicaltarget) >= (length bmpathologicalpat) of
            No  _         =>
              assert_total $ idris_crash "the target is shorter than the pattern"
            Yes lengthprf => do
              _ <-
                ( runIO $ \t =>
                    indicesBM bmpathologicalpat bmpathologicaltarget {prfpat=patprf} {prftarget=targetprf} {prflength=lengthprf} t)
              pure ()

indices_DFA : IO ()
indices_DFA =
  case decSo $ (not $ null dfapat) of
    No  _      =>
      assert_total $ idris_crash "pat is null"
    Yes patprf =>
      case decSo $ (not $ null dfatarget) of
        No  _         =>
          assert_total $ idris_crash "target is null"
        Yes targetprf => do
          _ <-
            ( runIO $ \t =>
                indicesDFA dfapat dfatarget {prfpat=patprf} {prftarget=targetprf} t)
          pure ()

indices_favoredKMP : IO ()
indices_favoredKMP =
  case decSo $ (not $ null kmpfavoredpat) of
    No  _      =>
      assert_total $ idris_crash "pat is null"
    Yes patprf =>
      case decSo $ (not $ null kmpfavoredtarget) of
        No  _         =>
          assert_total $ idris_crash "target is null"
        Yes targetprf => do
          _ <-
            ( runIO $ \t =>
                indicesKMP kmpfavoredpat kmpfavoredtarget {prfpat=patprf} {prftarget=targetprf} t)
          pure ()

indices_pathologicalKMP : IO ()
indices_pathologicalKMP =
  case decSo $ (not $ null kmppathologicalpat) of
    No  _      =>
      assert_total $ idris_crash "pat is null"
    Yes patprf =>
      case decSo $ (not $ null kmppathologicaltarget) of
        No  _         =>
          assert_total $ idris_crash "target is null"
        Yes targetprf => do
          _ <-
            ( runIO $ \t =>
                indicesKMP kmppathologicalpat kmppathologicaltarget {prfpat=patprf} {prftarget=targetprf} t)
          pure ()

bench : Benchmark Void
bench =
  Group "StringSearchAlgorithms"
    [ Group "Match"
        [ Group "BoyerMoore"
            [ Single "Favored (Pat: ZEBRAC, Target: TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT)"           (singleIO match_favoredBM)
            , Single "Pathological (Pat : AAAAAAAB, Target: AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA)" (singleIO match_pathologicalBM)
            ]
        , Group "DFA"
            [ Single "Favored<->Pathological (Pat: ABCD, Target: AABCAABCAABCAABCAABCAABC)" (singleIO match_DFA)
            ]
        , Group "KnuthMorrisPratt"
            [ Single "Favored (Pat: ABABACABABAC, Target: ABABACABABACABABACABABACABABACABABAC)"                      (singleIO match_favoredKMP)
            , Single "Pathological (Pat: ABCDEFGHIJKL, Target: AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA)" (singleIO match_pathologicalKMP)
            ]
        ]    
    , Group "Indices"
        [ Group "BoyerMoore"
            [ Single "Favored (Pat: ZEBRAC, Target: TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT)"           (singleIO indices_favoredBM)
            , Single "Pathological (Pat : AAAAAAAB, Target: AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA)" (singleIO indices_pathologicalBM)
            ]
        , Group "DFA"
            [ Single "Favored<->Pathological (Pat: ABCD, Target: AABCAABCAABCAABCAABCAABC)" (singleIO indices_DFA)
            ]
        , Group "KnuthMorrisPratt"
            [ Single "Favored (Pat: ABABACABABAC, Target: ABABACABABACABABACABABACABABACABABAC)"                      (singleIO indices_favoredKMP)
            , Single "Pathological (Pat: ABCDEFGHIJKL, Target: AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA)" (singleIO indices_pathologicalKMP)
            ]
        ]
    ]

main : IO ()
main = runDefault (const True) Details show bench
