(* 
    Standard Paremeter Identities 

    Authors: Ejean Kuo, Jonathan Lee
    Date: January 2026
*)
From SRG Require Import main.
From Stdlib Require Import ZArith.
Open Scope Z_scope.

(* Number of edges *)
(* There are 2 ways to find the number of edges between the neighbors and non-neighbors of mu: 
    Assuming G is a valid SRG: G = srg(n, k, lambda, mu). Then,
    1. There are k(k - mu - 1) non-neighbors of mu
    2. k(k - lambda - 1) = (n - k - 1)mu *)

Lemma srg_parameter_identity_1 (G : sgraph) (params : srg_params) :
    is_srg G params ->
    let v := Z.of_nat (srg_v params) in
    let k := srg_k params in
    let lam := srg_lambda params in
    let mu := srg_mu params in
    k * (k - lam - 1) = (v - k - 1) * mu.
Proof.
    
Qed.

    
(* Verifying edge count *)
(* If G is k-regular on v vertices, then it has vk/2 edges *)