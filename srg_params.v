(* 
    Standard Paremeter Identities 

    Authors: Ejean Kuo, Jonathan Lee
    Date: January 2026
*)
From SRG Require Import main.

(* Number of edges *)
(* There are 2 ways to find the number of edges between the neighbors and non-neighbors of mu: 
    Assuming G is a valid SRG: G = srg(n, k, lambda, mu). Then,
    1. There are k(k - mu - 1) non-neighbors of mu
    2. k(k - lambda - 1) = (n - k - 1)mu *)

Definition srg_parameter_identity_1 (G : sgraph) (params : srg_params) :
    is_srg G params ->
    let n := srg_v params in
    let k := srg_k params in
    let lam := srg_lambda params in
    let mu := srg_mu params in
    k * (k - lam - 1) = (n - k - 1) * mu.

    
(* Verifying edge count *)
(* If G is k-regular on v vertices, then it has vk/2 edges *)