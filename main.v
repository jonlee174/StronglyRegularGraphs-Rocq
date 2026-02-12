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

(** ** SRG Parameters Record *)

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
    2. G is k-regular
    3. Adjacent vertices have exactly lambda common neighbors
    4. Non-adjacent distinct vertices have exactly mu common neighbors *)
Definition is_srg (params : srg_params) : Prop :=
  [/\ #|[set: G]| = srg_v params,
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

Lemma x_notin_neighborhoodG (x : G) : x \notin neighborhood G x.
Proof. by rewrite /neighborhood inE sg_irrefl. Qed.

Lemma degree_compl (x : G) :
  @degree (compl G) x = #|G| - degree G x - 1.
Proof.
  rewrite /degree neighborhood_compl_eq.
  have Hsub: x |: neighborhood G x \subset [set: G] by apply/subsetP.
  rewrite -setTD cardsDS // cardsT cardsU1.
  by rewrite (negbTE (x_notin_neighborhoodG x)) /= subnDA subnAC.
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
  case/orP => /eqP ->.
  - by rewrite sg_sym Hadj orbT.
  - by rewrite Hadj.
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
  have Hdisj := set2_disj_union_neighborhoods_nonadj x y Hneq Hnonadj.
  rewrite cardsU (disjoint_setI0 Hdisj) cards0 subn0.
  rewrite cards2; rewrite Hneq /= cardsU.
  rewrite -/(degree G x) -/(degree G y) (Hreg x) (Hreg y).
  have->: #|neighborhood G x :&: neighborhood G y| = mu.
  { by rewrite -/(common_neighbors G x y) -/(num_common_neighbors G x y) Hmu. }
  by rewrite mul2n -addnn [2 + _]addnC.
Qed.

(* For adjacent x,y: |{x,y} U N(x) U N(y)| = 2k - lambda *)
Lemma card_union_adj (x y : G) (k lam : nat) :
  x != y -> x -- y ->
  is_regular G k ->
  (forall u v : G, u -- v -> num_common_neighbors G u v = lam) ->
  #|[set x; y] :|: (neighborhood G x :|: neighborhood G y)| = 2 * k - lam.
Proof.
  move=> Hneq Hadj Hreg Hlam.
  have Hsub := set2_sub_union_neighborhoods_adj x y Hadj.
  rewrite (setUidPr Hsub) cardsU.
  rewrite -/(degree G x) -/(degree G y) (Hreg x) (Hreg y).
  have->: #|neighborhood G x :&: neighborhood G y| = lam.
  { by rewrite -/(common_neighbors G x y) -/(num_common_neighbors G x y) Hlam. }
  by rewrite mul2n -addnn.
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

(* Arithmetic lemmas *)

(* This lemma handles nat subtraction for the non-adjacent case:
   v - (2*k - mu + 2) = v - 2*k + mu - 2  when appropriate bounds hold *)
Lemma nat_sub_rearrange (v k mu : nat) :
  mu <= 2 * k ->
  v - (2 * k - mu + 2) = v + mu - (2 * k + 2).
Proof.
  move=> Hmu_le.
  (* 2*k - mu + 2 = 2*k + 2 - mu when mu <= 2*k *)
  have H1: 2 * k - mu + 2 = 2 * k + 2 - mu.
  { rewrite addnC [2 * k + 2]addnC addnBA //. }
  rewrite H1.
  (* v - (2*k + 2 - mu) = v + mu - (2*k + 2) *)
  have Hmu_le': mu <= 2 * k + 2 by apply: leq_trans Hmu_le _; apply: leq_addr.
  by rewrite subnBA // addnC.
Qed.

(* For the final equality in the non-adjacent case *)
Lemma nat_arith_nonadj (v k mu : nat) :
  2 * k <= v ->
  v + mu - (2 * k + 2) = v - 2 * k + mu - 2.
Proof.
  move=> Hvk.
  set d := v - 2 * k.
  have Hv_eq: v = d + 2 * k by rewrite /d subnK.
  rewrite Hv_eq.
  rewrite [d + 2 * k + mu]addnAC.
  rewrite [2 * k + 2]addnC.
  rewrite subnDr.
  by [].
Qed.

(* Proves v - (2*k - mu + 2) = v - 2*k + mu - 2 *)
Lemma nat_sub_rearrange_full (v k mu : nat) :
  mu <= 2 * k ->
  2 * k <= v ->
  v - (2 * k - mu + 2) = v - 2 * k + mu - 2.
Proof.
  move=> Hmu_le Hvk.
  by rewrite nat_sub_rearrange // nat_arith_nonadj.
Qed.

(* 
   The complement closure theorem for SRGs.
   
   We require two arithmetic bounds that are always satisfied for valid SRGs:
   - lambda <= 2*k (since lambda <= k - 1 < k <= 2*k for k > 0)
   - mu <= 2*k (since mu <= k <= 2*k)
   
   And one bound ensuring the complement formula is well-defined:
   - 2*k <= v (which holds for all known SRGs)
*)
Theorem srg_complement_closure (params : srg_params) :
  srg_lambda params <= 2 * srg_k params ->
  srg_mu params <= 2 * srg_k params ->
  2 * srg_k params <= srg_v params ->
  is_srg G params -> 
  is_srg (compl G) (compl_srg_params params).
Proof.
  move=> Hlam_bound Hmu_bound Hv_ge_2k [Hv Hreg Hadj Hnonadj].
  rewrite /is_srg /compl_srg_params /=; split.
  - by rewrite Hv.
  
  - by move=> x; rewrite degree_compl -Hv cardsT (Hreg x).
  
  - move=> x y; rewrite /sedge /= => /andP[Hneq Hnotadj].
    rewrite /num_common_neighbors common_neighbors_compl //.
    rewrite card_compl_set.
    have Hcard := @card_union_nonadj x y (srg_k params) (srg_mu params) Hneq Hnotadj Hreg Hnonadj.
    rewrite Hcard.
    have->: #|[set: G]| = srg_v params by [].
    by apply: nat_sub_rearrange_full Hmu_bound Hv_ge_2k.
  
  - move=> x y Hneq.
    rewrite /sedge /= negb_and Hneq /= negbK => Hadj_G.
    rewrite /num_common_neighbors common_neighbors_compl //.
    rewrite card_compl_set.
    have Hcard := @card_union_adj x y (srg_k params) (srg_lambda params) Hneq Hadj_G Hreg Hadj.
    rewrite Hcard.
    have->: #|[set: G]| = srg_v params by [].
    set v := srg_v params; set k := srg_k params; set lam := srg_lambda params.
    rewrite subnBA //.
    rewrite addnC -addnBA // addnC.
    by [].
Qed.

End ComplementClosure.


(**  SRG Properties **)
(* Number of edges *)
(* There are 2 ways to find the number of edges between the neighbors and non-neighbors of mu: 
    Assuming G is a valid SRG: G = srg(n, k, lambda, mu). Then,
    1. There are k(k - lambda - 1) edges between the non-neighbors of mu
    2. k(k - lambda - 1) = (v - k - 1)mu *)
Section SRGProps.

Variable G : sgraph.
Variable p : srg_params.

Hypothesis H_srg : is_srg G p.

(* To ensure safe subtraction in k(k - lambda - 1) = (v - k - 1)mu, we need the following bounds:
    - k >= lambda + 1  || lambda < k
    - v >= k - 1 || k < v
*)
Hypothesis valid_k_lam : srg_lambda p < srg_k p.
Hypothesis valid_k_v : srg_k p < srg_v p.

Lemma srg_standard_parameter_identity :
  let v := srg_v p in
  let k := srg_k p in
  let lam := srg_lambda p in
  let mu := srg_mu p in
  k * (k - lam - 1) = (v - k - 1) * mu.
Proof.
  set v := srg_v p.
  set k := srg_k p.
  set lam := srg_lambda p.
  set mu := srg_mu p.

  move: H_srg => [Hv Hreg Hadj Hnonadj].

  (* Count the edges between neighbors and non-neighbors of a vertex x *)
  (* Let x be an arbitrary vertex in G *)
  have v_pos : 0 < v.
  { exact: (leq_ltn_trans (leq0n k) valid_k_v). }

  have cardV_pos : 0 < #|[set: G]|.
  { by rewrite Hv. }

  have [x _] : exists x : G, x \in [set: G].
  { by apply/card_gt0P. }

  pose N := neighborhood G x.
  pose M := [set y | (y != x) && (y \notin N)].

  (* Define neighbor/non-neighbor sets around x *)
  have size_N : #|N| = k.
  { have Hkx := Hreg x.
    by rewrite /degree /N in Hkx. }

  (* Size of M is v - k - 1 *)
  have size_M : #|M| = v - k - 1.


