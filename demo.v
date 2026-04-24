(*
    Concrete adjacency matrices for H(2,q) and Paley(p), computed by
    the formally verified graph constructions.

    Authors: Ejean Kuo, Jonathan Lee
    Date: March 2026
*)

From Corelib Require Extraction.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_field.
From GraphTheory.core Require Import edone preliminaries digraph sgraph.
Require Import SRG.main SRG.paley SRG.hamming.

Set Implicit Arguments.
Unset Printing Implicit Defensive.


(* Generic helper *)

Definition adj_matrix {A : eqType} (verts : seq A) (adj : A -> A -> bool)
  : seq (seq bool) :=
  [seq [seq adj u v | v <- verts] | u <- verts].


(* H(2,q) parametric extraction works cleanly *)

Definition hamming_verts (q : nat) := enum {: 'I_q * 'I_q}.

Definition hamming_mat (q : nat) :=
  adj_matrix (hamming_verts q) (@hamming_adj 'I_q).


(* Extraction                                                         *)

Extraction Language OCaml.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive nat => "int" [ "0" "succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "( * )" [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].

Extraction Blacklist String List.
Extraction Inline predT pred_of_argType.

Extraction "demo_srg.ml" hamming_mat.
