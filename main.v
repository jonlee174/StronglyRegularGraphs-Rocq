(*  
    This library provides a formalization of strongly regular graphs (SRGs)
    in the Rocq proof assistant, building on the coq-graph-theory library.
    
    Authors: Ejean Kuo, Jonathan Lee
    Date: January 2026
*)

From mathcomp Require Import all_ssreflect.
From GraphTheory.core Require Import edone preliminaries digraph sgraph.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

(* Basic Definitions *)

Section SRGDefinitions.

Variable G : sgraph.

Definition neighborhood (x : G) : {set G} := [set y | x -- y].
Definition degree (x : G) := #|neighborhood x|.
Definition common_neighbors (x y : G) : {set G} := neighborhood x :&: neighborhood y.
Definition num_common_neighbors (x y : G) := #|common_neighbors x y|.
Definition is_regular (k : nat) := forall x : G, degree x = k.

End SRGDefinitions.

Record srg_params := SRGParams {
  srg_v : nat;
  srg_k : nat;
  srg_lambda : nat;
  srg_mu : nat
}.

Section SRGPredicate.

Variable G : sgraph.

(* A graph G is strongly regular with parameters (v, k, lambda, mu) if:
    1. G has exactly v vertices
    2. G is connected
    3. G is k-regular
    4. Adjacent vertices have exactly lambda common neighbors
    5. Non-adjacent distinct vertices have exactly mu common neighbors *)
Definition is_srg (params : srg_params) : Prop :=
  [/\ #|[set: G]| = srg_v params,
      connected [set: G],
      is_regular G (srg_k params),
      (forall x y : G, x -- y -> num_common_neighbors G x y = srg_lambda params) &
      (forall x y : G, x != y -> ~~ (x -- y) -> num_common_neighbors G x y = srg_mu params)].

End SRGPredicate.

Record SRGraph := {
  srg_graph :> sgraph;
  srg_params_of : srg_params;
  srg_proof : is_srg srg_graph srg_params_of
}.


Section NeighborhoodLemmas.

Variable G : sgraph.

Lemma not_in_neighborhood (x : G) : x \notin neighborhood G x.
Proof. by rewrite /neighborhood inE sg_irrefl. Qed.

Lemma neighborhood_sym (x y : G) : 
  (x \in neighborhood G y) = (y \in neighborhood G x).
Proof. by rewrite /neighborhood !inE sg_sym. Qed.

Lemma common_neighbors_sym (x y : G) :
  common_neighbors G x y = common_neighbors G y x.
Proof. by rewrite /common_neighbors setIC. Qed.

Lemma num_common_neighbors_sym (x y : G) :
  num_common_neighbors G x y = num_common_neighbors G y x.
Proof. by rewrite /num_common_neighbors common_neighbors_sym. Qed.

Lemma common_neighbors_sub_neighborhood (x y : G) :
  common_neighbors G x y \subset neighborhood G x.
Proof. by apply/subsetP => z; rewrite /common_neighbors inE => /andP[]. Qed.

End NeighborhoodLemmas.


Section ComplementClosure.

Variable G : sgraph.

(* Neighborhood lemmas for the complement graph *)

Lemma neighborhood_compl (x : G) :
  @neighborhood (compl G) x = [set y : G | (y != x) && ~~ (x -- y)].
Proof. by apply/setP => y; rewrite /neighborhood !inE eq_sym. Qed.

Lemma neighborhood_compl_eq (x : G) :
  @neighborhood (compl G) x = ~: (x |: neighborhood G x).
Proof. by apply/setP => y; rewrite neighborhood_compl !inE negb_or. Qed.

Lemma degree_compl (x : G) :
  @degree (compl G) x = #|G| - degree G x - 1.
Proof.
  rewrite /degree neighborhood_compl_eq -setTD cardsDS ?cardsT ?cardsU1;
    last by apply/subsetP.
  by rewrite (negbTE (not_in_neighborhood G x)) /= subnDA subnAC.
Qed.

Lemma common_neighbors_compl (x y : G) (Hneq : x != y) :
  @common_neighbors (compl G) x y =
    ~: ([set x; y] :|: (neighborhood G x :|: neighborhood G y)).
Proof.
  apply/setP => z.
  rewrite /common_neighbors !neighborhood_compl_eq !inE !negb_or.
  by case: (z == x); case: (z == y);
     case: (z \in neighborhood G x); case: (z \in neighborhood G y).
Qed.

Lemma adj_in_neighborhood (x y : G) : x -- y -> y \in neighborhood G x.
Proof. by rewrite /neighborhood inE. Qed.

(* Disjointness lemmas *)

Lemma set2_disj_union_neighborhoods_nonadj (x y : G) :
  x != y -> ~~ (x -- y) ->
  [disjoint [set x; y] & neighborhood G x :|: neighborhood G y].
Proof.
  move=> Hneq Hnonadj; rewrite -setI_eq0; apply/eqP/setP => z.
  rewrite /neighborhood !inE.
  case/boolP: (z == x) => [/eqP -> | _].
  - by rewrite sg_irrefl sg_sym (negbTE Hnonadj).
  - case/boolP: (z == y) => [/eqP -> | _] //.
    by rewrite sg_irrefl (negbTE Hnonadj) orbF.
Qed.

(* When x and y are adjacent, {x,y} \subset N(x) U N(y) *)
Lemma set2_sub_union_neighborhoods_adj (x y : G) :
  x -- y -> [set x; y] \subset neighborhood G x :|: neighborhood G y.
Proof.
  move=> Hadj; apply/subsetP => z; rewrite /neighborhood !inE.
  by case/orP => /eqP ->; [rewrite (sg_sym y) Hadj orbT | rewrite Hadj].
Qed.

(* Cardinality of unions *)

(* For non-adjacent x,y: |{x,y} U N(x) U N(y)| = 2 + 2k - mu *)
Lemma card_union_nonadj (x y : G) (k mu : nat) :
  x != y -> ~~ (x -- y) ->
  is_regular G k ->
  (forall u v : G, u != v -> ~~ (u -- v) -> num_common_neighbors G u v = mu) ->
  #|[set x; y] :|: (neighborhood G x :|: neighborhood G y)| = 2 * k - mu + 2.
Proof.
  move=> Hneq Hnonadj Hreg Hmu.
  rewrite cardsU (disjoint_setI0 (set2_disj_union_neighborhoods_nonadj _ _ Hneq Hnonadj)).
  rewrite cards0 subn0 cards2 Hneq /= cardsU.
  rewrite -/(degree G x) -/(degree G y) (Hreg x) (Hreg y).
  by rewrite -/(common_neighbors G x y) -/(num_common_neighbors G x y) Hmu // mul2n -addnn [2 + _]addnC.
Qed.

(* For adjacent x,y: |{x,y} U N(x) U N(y)| = 2k - lambda *)
Lemma card_union_adj (x y : G) (k lam : nat) :
  x != y -> x -- y ->
  is_regular G k ->
  (forall u v : G, u -- v -> num_common_neighbors G u v = lam) ->
  #|[set x; y] :|: (neighborhood G x :|: neighborhood G y)| = 2 * k - lam.
Proof.
  move=> Hneq Hadj Hreg Hlam.
  rewrite (setUidPr (set2_sub_union_neighborhoods_adj _ _ Hadj)) cardsU.
  rewrite -/(degree G x) -/(degree G y) (Hreg x) (Hreg y).
  by rewrite -/(common_neighbors G x y) -/(num_common_neighbors G x y) Hlam // mul2n -addnn.
Qed.

(* Complement parameters *)

Definition compl_srg_params (params : srg_params) : srg_params :=
  let n := srg_v params in
  let k := srg_k params in
  let lam := srg_lambda params in
  let mu := srg_mu params in
  SRGParams n (n - k - 1) (n - 2 * k + mu - 2) (n - 2 * k + lam).

Lemma card_compl_set (A : {set G}) : #|~: A| = #|[set: G]| - #|A|.
Proof. by rewrite -setTD cardsDS //; apply/subsetP. Qed.

(* Arithmetic for nat subtraction rearrangement: v - (2*k - mu + 2) = v - 2*k + mu - 2  *)
Lemma nat_sub_rearrange (v k mu : nat) :
  mu <= 2 * k -> 2 * k <= v ->
  v - (2 * k - mu + 2) = v - 2 * k + mu - 2.
Proof.
  by move=> Hmu Hvk; rewrite subnDA (subnBA v Hmu) (addnC v) -(addnBA mu Hvk) addnC.
Qed.

Theorem srg_complement_closure (params : srg_params) :
  srg_lambda params <= 2 * srg_k params ->
  srg_mu params <= 2 * srg_k params ->
  2 * srg_k params <= srg_v params ->
  connected [set: compl G] ->
  is_srg G params -> 
  is_srg (compl G) (compl_srg_params params).
Proof.
  move=> Hlam_bound Hmu_bound Hv_ge_2k Hconn_compl [Hv Hconn Hreg Hadj Hnonadj].
  rewrite /is_srg /compl_srg_params /=; split.
  - by rewrite Hv.
  - exact: Hconn_compl.
  - by move=> x; rewrite degree_compl -Hv cardsT (Hreg x).
  - move=> x y; rewrite /sedge /= => /andP[Hneq Hnotadj].
    rewrite /num_common_neighbors common_neighbors_compl // card_compl_set.
    rewrite (card_union_nonadj _ _ Hneq Hnotadj Hreg Hnonadj).
    by have->: #|[set: G]| = srg_v params by []; exact: nat_sub_rearrange.
  - move=> x y Hneq; rewrite /sedge /= negb_and Hneq /= negbK => Hadj_G.
    rewrite /num_common_neighbors common_neighbors_compl // card_compl_set.
    rewrite (card_union_adj _ _ Hneq Hadj_G Hreg Hadj).
    by have->: #|[set: G]| = srg_v params by []; rewrite subnBA // addnC -addnBA // addnC.
Qed.

End ComplementClosure.


Section EdgeCount.

Variable G : sgraph.

Lemma card_setI_sum (A B : {set G}) : #|A :&: B| = \sum_(z in A) (z \in B).
Proof.
  rewrite -sum1_card.
  under eq_bigl => z do rewrite inE.
  by rewrite big_mkcondr.
Qed.

(* Counting edges between N(x) and the rest of the graph in two directions *)
Lemma srg_edge_count (k lam mu : nat) (x : G) :
  is_regular G k ->
  (forall u v : G, u -- v -> num_common_neighbors G u v = lam) ->
  (forall u v : G, u != v -> ~~ (u -- v) -> num_common_neighbors G u v = mu) ->
  (#|~: (neighborhood G x :|: [set x])| * mu + k * lam.+1 = k * k)%N.
Proof.
  move=> Hreg Hlam Hmu.
  pose D := ~: (neighborhood G x :|: [set x]).
  have HNx : #|neighborhood G x| = k by rewrite -/(degree G x) Hreg.
  have Hkey : (\sum_(y in neighborhood G x) #|neighborhood G y :&: D|
             = \sum_(z in D) #|neighborhood G z :&: neighborhood G x|)%N.
  { under eq_bigr => y _ do rewrite setIC card_setI_sum.
    under [RHS]eq_bigr => z _ do rewrite setIC card_setI_sum.
    rewrite exchange_big /=; apply: eq_bigr => z _; apply: eq_bigr => y _.
    by rewrite !inE sg_sym. }
  have HR : (\sum_(z in D) #|neighborhood G z :&: neighborhood G x|
             = #|D| * mu)%N.
  { rewrite -sum_nat_const; apply: eq_bigr => z Hz.
    move: Hz; rewrite /D !inE negb_or => /andP[Hnadj Hzx].
    have Hm := Hmu z x Hzx; rewrite /num_common_neighbors /common_neighbors in Hm.
    by apply: Hm; rewrite sg_sym. }
  have HL : (\sum_(y in neighborhood G x) #|neighborhood G y :&: D|
             + #|neighborhood G x| * lam.+1 = #|neighborhood G x| * k)%N.
  { rewrite -!sum_nat_const -big_split /=; apply: eq_bigr => y Hy.
    have Hxy : x -- y by move: Hy; rewrite inE.
    have Hyx0 : y -- x by rewrite sg_sym.
    have Hyx : x \in neighborhood G y by rewrite inE.
    have Hyk : #|neighborhood G y| = k by rewrite -/(degree G y) Hreg.
    have Hl := Hlam y x Hyx0.
    rewrite /num_common_neighbors /common_neighbors in Hl.
    have HD : neighborhood G y :\: D = x |: (neighborhood G y :&: neighborhood G x).
    { apply/setP => z; rewrite /D !inE negbK.
      case: (altP (z =P x)) => [->|Hzx].
      - by rewrite orbT /= Hyx0.
      - by rewrite orbF andbC. }
    have Hxni : x \notin neighborhood G y :&: neighborhood G x
      by rewrite inE negb_and not_in_neighborhood orbT.
    have Hc := cardsID D (neighborhood G y).
    by rewrite HD cardsU1 Hxni /= add1n Hyk Hl in Hc. }
  by rewrite HNx in HL; rewrite -/D -HR -Hkey.
Qed.

End EdgeCount.
