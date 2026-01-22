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

(* The neighborhood of a vertex: the set of all adjacent vertices *)
Definition neighborhood (x : G) : {set G} :=
  [set y | x -- y].

(* Degree of a vertex: number of neighbors *)
Definition degree (x : G) := #|neighborhood x|.

(* Common neighbors of two vertices *)
Definition common_neighbors (x y : G) : {set G} :=
  neighborhood x :&: neighborhood y.

(* Number of common neighbors *)
Definition num_common_neighbors (x y : G) := #|common_neighbors x y|.

(* A graph is regular with degree k if every vertex has exactly k neighbors *)
Definition is_regular (k : nat) :=
  forall x : G, degree x = k.

End SRGDefinitions.

(** ** SRG Parameters Record *)

Record srg_params := SRGParams {
  srg_v : nat;
  srg_k : nat;
  srg_lambda : nat;
  srg_mu : nat
}.

(** ** Strongly Regular Graph Predicate *)

Section SRGPredicate.

Variable G : sgraph.

(* A graph G is strongly regular with parameters (v, k, lambda, mu) if:
    1. G has exactly v vertices
    2. G is k-regular
    3. Adjacent vertices have exactly lambda common neighbors
    4. Non-adjacent distinct vertices have exactly mu common neighbors *)
Definition is_srg (params : srg_params) : Prop :=
  let v := srg_v params in
  let k := srg_k params in
  let lam := srg_lambda params in
  let mu := srg_mu params in
  [/\ #|[set: G]| = v,
      is_regular G k,
      (forall (x y : G), x -- y -> num_common_neighbors G x y = lam) &
      (forall (x y : G), x != y -> ~~ (x -- y) -> num_common_neighbors G x y = mu)].

End SRGPredicate.

(* Accessor functions for SRG parameters *)
Definition srg_num_vertices (S : SRGraph) := srg_v (srg_params_of S).
Definition srg_degree (S : SRGraph) := srg_k (srg_params_of S).
Definition srg_adj_common (S : SRGraph) := srg_lambda (srg_params_of S).
Definition srg_nonadj_common (S : SRGraph) := srg_mu (srg_params_of S).

(* Basic Lemmas about Neighborhoods *)

Section NeighborhoodLemmas.

Variable G : sgraph.

(* A vertex is not in its own neighborhood (irreflexivity) *)
Lemma not_in_neighborhood (x : G) : x \notin neighborhood G x.
Proof.
  rewrite /neighborhood inE.
  by rewrite sg_irrefl.
Qed.

(* Neighborhood is symmetric *)
Lemma neighborhood_sym (x y : G) : 
  (x \in neighborhood G y) = (y \in neighborhood G x).
Proof.
  rewrite /neighborhood !inE.
  by rewrite sg_sym.
Qed.

(* Common neighbors is symmetric *)
Lemma common_neighbors_sym (x y : G) :
  common_neighbors G x y = common_neighbors G y x.
Proof.
  rewrite /common_neighbors.
  by rewrite setIC.
Qed.

(* Number of common neighbors is symmetric *)
Lemma num_common_neighbors_sym (x y : G) :
  num_common_neighbors G x y = num_common_neighbors G y x.
Proof.
  by rewrite /num_common_neighbors common_neighbors_sym.
Qed.

End NeighborhoodLemmas.
