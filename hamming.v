(*
    The Hamming graph H(2,q) (lattice graph L_2(q), or q x q grid) is
    strongly regular with parameters (q^2, 2(q − 1), q − 2, 2) for q >= 2.

    Vertices are pairs from T x T where #|T| = q.  Two vertices are
    adjacent iff they agree in exactly one coordinate.

    Authors: Ejean Kuo, Jonathan Lee
    Date: March 2026
*)

From mathcomp Require Import all_ssreflect.
From GraphTheory.core Require Import edone preliminaries digraph sgraph.
Require Import main.

Set Implicit Arguments.
Unset Printing Implicit Defensive.


Section HammingGraph.

Variable T : finType.
Let q := #|T|.

Hypothesis q_ge_2 : (2 <= q)%N.


(* Adjacency *)

Definition hamming_adj (u v : T * T) : bool :=
  ((u.1 == v.1) && (u.2 != v.2)) || ((u.1 != v.1) && (u.2 == v.2)).

Lemma hamming_irrefl (u : T * T) : hamming_adj u u = false.
Proof. by rewrite /hamming_adj !eq_refl andbF. Qed.

Lemma hamming_sym (u v : T * T) : hamming_adj u v = hamming_adj v u.
Proof. by rewrite /hamming_adj !(eq_sym u.1) !(eq_sym u.2). Qed.

Definition hamming_graph : sgraph := SGraph hamming_sym hamming_irrefl.


(* Adjacency characterisations *)

Lemma nonadj_both_diff (u v : T * T) :
  u != v -> ~~ hamming_adj u v -> (u.1 != v.1) && (u.2 != v.2).
Proof.
  rewrite /hamming_adj negb_or !negb_and.
  by case: (u.1 != v.1); case: (u.2 != v.2).
Qed.


(* Neighborhood *)

Lemma neighborhood_eq (u : T * T) :
  @neighborhood hamming_graph u =
  setX [set u.1] ([set: T] :\ u.2) :|: setX ([set: T] :\ u.1) [set u.2].
Proof.
  apply/setP => [[v1 v2]] /=.
  rewrite /neighborhood inE /= /hamming_adj in_setU !in_setX.
  by rewrite !in_set1 !inE (eq_sym v1 u.1) (eq_sym v2 u.2).
Qed.

Lemma row_col_disjoint (u : T * T) :
  [disjoint setX [set u.1] ([set: T] :\ u.2)
          & setX ([set: T] :\ u.1) [set u.2]].
Proof.
  rewrite -setI_eq0; apply/eqP/setP => [[v1 v2]] /=.
  rewrite in_setI !in_setX !in_set1 !inE.
  by case: (v1 == u.1); case: (v2 == u.2).
Qed.

Lemma card_remove1 (A : {set T}) (a : T) : a \in A -> #|A :\ a| = #|A|.-1.
Proof. by move=> Ha; have := cardsD1 a A; rewrite Ha add1n => ->. Qed.

Lemma cardT_remove1 (a : T) : #|[set: T] :\ a| = q.-1.
Proof. by rewrite card_remove1 ?inE // /q cardsT. Qed.


(* Degree *)

Lemma hamming_degree (u : T * T) :
  @degree hamming_graph u = 2 * (q - 1).
Proof.
  rewrite /degree neighborhood_eq cardsU (disjoint_setI0 (row_col_disjoint u)).
  rewrite cards0 subn0.
  have card1 : #|setX [set u.1] ([set: T] :\ u.2)| = q - 1.
  { by rewrite cardsX cards1 (cardT_remove1 u.2) mul1n subn1. }
  have card2 : #|setX ([set: T] :\ u.1) [set u.2]| = q - 1.
  { by rewrite cardsX (cardT_remove1 u.1) cards1 muln1 subn1. }
  by rewrite card1 card2 addnn mul2n.
Qed.

Lemma hamming_regular : @is_regular hamming_graph (2 * (q - 1)).
Proof. by move=> x; exact: hamming_degree. Qed.


(* Lambda *)

Lemma cn_same_row (u v : T * T) :
  u.1 = v.1 -> u.2 != v.2 ->
  @common_neighbors hamming_graph u v =
  setX [set u.1] (([set: T] :\ u.2) :\ v.2).
Proof.
  move=> Heq1 Hne2; apply/setP => [[w1 w2]].
  rewrite /common_neighbors /neighborhood !inE /edge_rel /= /hamming_adj.
  rewrite Heq1 !(eq_sym w1) !(eq_sym w2).
  case: (v.1 == w1) => /=.
  - by rewrite andbC.
  - by case: (u.2 =P w2) => [<- | _] //=; rewrite eq_sym (negbTE Hne2).
Qed.

Lemma cn_same_col (u v : T * T) :
  u.1 != v.1 -> u.2 = v.2 ->
  @common_neighbors hamming_graph u v =
  setX (([set: T] :\ u.1) :\ v.1) [set u.2].
Proof.
  move=> Hne1 Heq2; apply/setP => [[w1 w2]].
  rewrite /common_neighbors /neighborhood !inE /edge_rel /= /hamming_adj.
  rewrite Heq2 !(eq_sym w1) !(eq_sym w2).
  case: (v.2 == w2) => /=.
  - by rewrite andbC.
  - by case: (u.1 =P w1) => [<- | _] //=; rewrite eq_sym (negbTE Hne1).
Qed.

Lemma hamming_lambda (u v : T * T) :
  @sedge hamming_graph u v ->
  @num_common_neighbors hamming_graph u v = (q - 2)%N.
Proof.
  rewrite /= /hamming_adj => /orP[/andP[/eqP Heq1 Hne2] | /andP[Hne1 /eqP Heq2]].
  - rewrite /num_common_neighbors (cn_same_row _ _ Heq1 Hne2).
    rewrite cardsX cards1 mul1n.
    have Hv2 : v.2 \in ([set: T] :\ u.2) by rewrite !inE eq_sym Hne2.
    by rewrite (card_remove1 Hv2) (cardT_remove1 u.2) -!subn1 -subnDA.
  - rewrite /num_common_neighbors (cn_same_col _ _ Hne1 Heq2).
    rewrite cardsX cards1 muln1.
    have Hv1 : v.1 \in ([set: T] :\ u.1) by rewrite !inE eq_sym Hne1.
    by rewrite (card_remove1 Hv1) (cardT_remove1 u.1) -!subn1 -subnDA.
Qed.


(* Mu *)

Lemma cn_both_diff (u v : T * T) :
  u.1 != v.1 -> u.2 != v.2 ->
  @common_neighbors hamming_graph u v = [set (u.1, v.2); (v.1, u.2)].
Proof.
  move=> Hne1 Hne2; apply/setP => [[w1 w2]].
  rewrite /common_neighbors /neighborhood !inE /edge_rel /= /hamming_adj !xpair_eqE.
  case: (w1 =P u.1) => [-> | /eqP Hw1u];
  case: (w2 =P u.2) => [-> | /eqP Hw2u] /=;
  rewrite ?eq_refl ?(negbTE Hne1) ?(negbTE Hne2) //=.
  - by rewrite !orbF (eq_sym v.1) (negbTE Hne1) /= (eq_sym w2);
    case: (v.2 == w2); rewrite //= eq_sym (negbTE Hw2u).
  - rewrite !andbT !andbF orFb (eq_sym w1).
    case: (v.1 =P w1) => [<- | /eqP Hw1v] /=.
    + by rewrite orbF Hne1 eq_sym Hne2.
    + by rewrite (eq_sym v.2) (negbTE Hne2) andbF.
  - rewrite andbF.
    case: (w1 =P v.1) => [-> | /eqP Hw1v] /=.
    + by rewrite (negbTE Hne1) /= eq_refl /= (eq_sym u.2) (negbTE Hw2u).
    + by rewrite (eq_sym u.1) (negbTE Hw1u) (eq_sym u.2) (negbTE Hw2u).
Qed.

Lemma hamming_mu (u v : T * T) :
  u != v -> ~~ @sedge hamming_graph u v ->
  @num_common_neighbors hamming_graph u v = 2.
Proof.
  move=> Hneq Hnadj.
  have /andP[Hne1 Hne2] := @nonadj_both_diff u v Hneq (Hnadj : ~~ hamming_adj u v).
  rewrite /num_common_neighbors (cn_both_diff _ _ Hne1 Hne2).
  by rewrite cards2 xpair_eqE (negbTE Hne1).
Qed.


(* Connectivity *)

Lemma hamming_connected : connected [set: hamming_graph].
Proof.
  apply: connectedTI => u v.
  case: (u =P v) => [->|/eqP Hneq]; first exact: connect0.
  case Hadj: (u -- v); first exact: connect1.
  have Hmu := hamming_mu _ _ Hneq (negbT Hadj).
  have [w Hw] : exists w, w \in @common_neighbors hamming_graph u v.
  { by apply/card_gt0P; rewrite -/(num_common_neighbors _ _ _) Hmu. }
  move: Hw; rewrite /common_neighbors /neighborhood !inE => /andP[Huw Hvw].
  apply: connect_trans (connect1 Huw) _; by apply: connect1; rewrite sg_sym.
Qed.


(* SRG *)

Definition hamming_params : srg_params :=
  SRGParams (q * q) (2 * (q - 1)) (q - 2) 2.

Theorem hamming_is_srg : is_srg hamming_graph hamming_params.
Proof.
  rewrite /is_srg /hamming_params /=; split.
  - by rewrite cardsE card_prod.
  - exact: hamming_connected.
  - exact: hamming_regular.
  - exact: hamming_lambda.
  - exact: hamming_mu.
Qed.


(* Complement *)

Lemma hamming_lam_le_2k : (q - 2 <= 2 * (2 * (q - 1)))%N.
Proof.
  apply: leq_trans (leq_subr 2 q) _.
  rewrite mulnA mulnBr muln1 leq_subRL; last first.
  { by rewrite leq_pmulr // (ltn_trans _ q_ge_2). }
  apply: leq_trans (_ : 2 * q + q <= _).
  - by rewrite leq_add2r leq_mul2l q_ge_2 orbT.
  - by rewrite addnC -mulSn leq_mul2r orbT.
Qed.

Lemma hamming_mu_le_2k : (2 <= 2 * (2 * (q - 1)))%N.
Proof.
  by rewrite mulnA -[X in X <= _]muln1; apply: leq_mul => //; rewrite subn_gt0.
Qed.

Lemma hamming_2k_le_v : (2 * (2 * (q - 1)) <= q * q)%N.
Proof.
  case: q q_ge_2 => [|[|[|[|n]]]] // _.
  rewrite mulnA subn1 /= [n.+4 * n.+4]mulnS.
  by apply: leq_trans (leq_addl _ _); rewrite leq_mul2r orbT.
Qed.

Definition hamming_compl_params := compl_srg_params hamming_params.

(* For q = 2 the complement is the empty graph on 4 vertices (k_compl = 0),
   so it's disconnected. For q >= 3 the complement should be connected
   since compl_k = (q-1)^2 >= 4, but we haven't proved this yet *)

Theorem hamming_compl_is_srg :
  connected [set: compl hamming_graph] ->
  is_srg (compl hamming_graph) hamming_compl_params.
Proof.
  move=> Hconn; rewrite /hamming_compl_params.
  apply: (@srg_complement_closure hamming_graph hamming_params) => //.
  - exact: hamming_lam_le_2k.
  - exact: hamming_mu_le_2k.
  - exact: hamming_2k_le_v.
  - exact: hamming_is_srg.
Qed.

End HammingGraph.
