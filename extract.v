(*
    Extraction of SRG library and Paley and Hamming graph constructions to OCaml.

    Authors: Ejean Kuo, Jonathan Lee
    Date: March 2026
*)

From Corelib Require Extraction.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_field.
From GraphTheory.core Require Import edone preliminaries digraph sgraph.
Require Import SRG.main SRG.paley SRG.hamming.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Extraction Language OCaml.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive nat => "int" [ "0" "succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "( * )" [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].

Extraction Blacklist String List.
Extraction Inline predT pred_of_argType.

Extraction "srg.ml"
  neighborhood degree common_neighbors num_common_neighbors is_regular
  srg_params SRGParams is_srg compl_srg_params srg_complement_closure
  is_QR paley_adj paley_graph paley_degree paley_regular
  paley_params paley_is_srg paley_compl_params paley_compl_is_srg
  hamming_adj hamming_graph hamming_regular
  hamming_params hamming_is_srg hamming_compl_is_srg.