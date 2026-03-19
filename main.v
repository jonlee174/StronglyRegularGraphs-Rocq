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


(**  SRG Properties **)
(* Number of edges *)
(* There are 2 ways to find the number of edges between the neighbors and non-neighbors of mu: 
    Assuming G is a valid SRG: G = srg(n, k, lambda, mu). Then,
    1. There are k(k - lambda - 1) edges between the non-neighbors of u
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

(* General lemma for bipartite graph *)
Lemma bipartite_g (A B : {set G}) (a b : nat) :
  [disjoint A & B] ->
  (forall v, v \in A -> #|neighborhood G v :&: B| = a) ->
  (forall v, v \in B -> #|neighborhood G v :&: A| = b) ->
  #|A| * a = #|B| * b.
Proof.
  Admitted.


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
  have num_v : 0 < v.
  { exact: (leq_ltn_trans (leq0n k) valid_k_v). }

  have [x _] : exists x : G, x \in [set: G].
  { apply/card_gt0P.
    rewrite Hv.
    exact: num_v.
  }

  (* Define neighbor/non-neighbor sets around x *)
  pose N := neighborhood G x.
  pose M := [set y | (y != x) && (y \notin N)].

  have size_N : #|N| = k.
  { have Hkx := Hreg x.
    by rewrite /degree /N in Hkx. }

  (* Size of M is v - k - 1 *)
  have size_M : #|M| = v - k - 1.
  { rewrite /M.
    rewrite (_ : [set y | (y != x) && (y \notin N)] = ~: (x |: N)).
    - rewrite card_compl_set.
      rewrite cardsU1.
      rewrite Hv size_N -/v.
      rewrite not_in_neighborhood.
      rewrite addnC.
      by rewrite subnDA.
    - apply/setP => z.
      rewrite !inE.
      rewrite negb_or.
      by rewrite eq_sym.
  }

  (* Counting number of edges connecting N to M:
      - Step 1: prove that for a bipartite graph with 
        parts A and B which is bi-regular of degrees
        (a, b), the number of edges is a|A| = b|B|. 
      - Step 2: apply this to N(x) and M(x) (ie, (V - N(x) - {x}) )
  *)
  rewrite /v /k /lam /mu.

  (* Step 2: *)
  have bipartite_N_M : #|N| * (srg_k p - srg_lambda p - 1) = #|M| * (srg_mu p).
  { refine (bipartite_g (A := N) (B := M) 
                        (a := srg_k p - srg_lambda p - 1) 
                        (b := srg_mu p) _ _ _).
    - (* Subgoal: Disjointness of N and M *)
      rewrite /N /M.
      apply/disjointP => z.
      rewrite !inE.
      move => H_in_N /andP [_ H_not_in_N].
      by rewrite H_in_N in H_not_in_N.

    - (* Subgoal 2: Fixed degree from N to M *)
      move=> z Hz.
      have Hzx : z -- x by move: Hz; rewrite /N /neighborhood inE sg_sym.
      pose sub_set := x |: (neighborhood G z :&: N).

      have -> : neighborhood G z :&: M = neighborhood G z :\: sub_set.
      { apply/setP=> w. rewrite /sub_set /M /N !inE !negb_or.
        by case: (z -- w). }
      
      have Hsub : sub_set \subset neighborhood G z.
      { apply/subsetP=> w. rewrite /sub_set !inE.
        case/orP=> [/eqP -> | /andP[H _]] //. }

      rewrite (cardsDS Hsub).

      have -> : #|sub_set| = 1 + srg_lambda p.
      { rewrite /sub_set cardsU1.
        have -> : x \notin neighborhood G z :&: N = true.
        { rewrite in_setI.
          have Hx : (x \in N) = false by rewrite /N inE sg_irrefl.
          by rewrite Hx andbF. }
        by rewrite -/(num_common_neighbors G z x) (Hadj z x Hzx). }

        have -> : #|neighborhood G z| = srg_k p by exact: (Hreg z).
        by rewrite addnC subnDA.

    - (* Subgoal 3: Fixed degree from M to N *)
      move=> z Hz.
      have Hneq : z != x by move: Hz; rewrite /M inE => /andP [H _].
      have HnotN : z \notin N by move: Hz; rewrite /M inE => /andP [_ H].
      have Hnotadj : ~~ (z -- x).
      { move: HnotN. rewrite /N inE. 
        by rewrite sg_sym. }
      have -> : #|neighborhood G z :&: N| = num_common_neighbors G z x.
      { by rewrite /N /num_common_neighbors. }
      by exact: (Hnonadj z x Hneq Hnotadj).
  }
  by rewrite size_N size_M in bipartite_N_M.
Qed.
      
  