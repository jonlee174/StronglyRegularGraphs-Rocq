(*
    CLI driver: compute and print adjacency matrices for Hamming and
    Paley graphs using the formally verified, extracted constructions.

    Usage:  ./demo hamming <q>     - H(2,q), q >= 2
            ./demo paley  <p>     - Paley(p), p prime, p = 1 (mod 4)

    Authors: Ejean Kuo, Jonathan Lee
    Date: March 2026
*)

(* Output *)

let print_matrix (mat : bool list list) =
  List.iter (fun row ->
    List.iter (fun b -> print_char (if b then '1' else '0')) row;
    print_newline ()
  ) mat


(* H(2,q) - Demo_srg.hamming_mat wraps the verified hamming_adj over 'I_q *)

let hamming_matrix q = Demo_srg.hamming_mat q


(* Paley(p) - 'F_p cannot be extracted directly (its field structure carries a
   Prop-sorted prod, which Coq extraction rejects), so we hand-build the
   FinRing.Field record for Z/pZ and call the verified Srg.paley_adj on it.
   Every operation below is a genuine field operation on Z/pZ for prime p;
   the Prop-only mixins erase to Axioms_ placeholders. *)

module Fp = struct
  let repr (x : int) : Obj.t = Obj.repr x
  let obj (x : Obj.t) : int = Obj.obj x

  let add p x y = repr ((obj x + obj y) mod p)
  let opp p x = repr ((p - obj x) mod p)
  let mul p x y = repr ((obj x * obj y) mod p)
  let eq x y = obj x = obj y

  (* x^n mod p by square and multiply *)
  let rec pow p b n =
    if n = 0 then 1
    else
      let h = pow p b (n / 2) in
      let h2 = h * h mod p in
      if n mod 2 = 0 then h2 else h2 * b mod p

  (* Fermat: for prime p and x <> 0, x^(p-2) is the inverse of x *)
  let inv p x = if obj x = 0 then repr 0 else repr (pow p (obj x) (p - 2))
end

let fp_instance (p : int) : Srg.FinRing.Field.coq_type =
  Obj.magic
    { Srg.FinRing.Field.coq_Algebra_hasOpp_mixin = Fp.opp p;
      coq_Algebra_hasZero_mixin = Fp.repr 0;
      coq_Algebra_hasAdd_mixin = Fp.add p;
      coq_Algebra_BaseZmoduleNmodule_isZmodule_mixin =
        Srg.Algebra.BaseZmoduleNmodule_isZmodule.Axioms_;
      coq_Algebra_BaseAddUMagma_isAddUMagma_mixin =
        Srg.Algebra.BaseAddUMagma_isAddUMagma.Axioms_;
      coq_Algebra_BaseAddMagma_isAddMagma_mixin =
        Srg.Algebra.BaseAddMagma_isAddMagma.Axioms_;
      choice_hasChoice_mixin =
        Obj.magic (fun (q : Obj.t -> bool) (n : int) ->
          if n < p && q (Fp.repr n) then Some (Fp.repr n) else None);
      choice_Choice_isCountable_mixin =
        { Srg.Choice_isCountable.pickle = Obj.magic (fun (x : int) -> x);
          unpickle = Obj.magic (fun (n : int) ->
            if 0 <= n && n < p then Some (Fp.repr n) else None) };
      eqtype_hasDecEq_mixin =
        { Srg.Coq_hasDecEq.eq_op = Fp.eq;
          eqP = (fun x y -> if Fp.eq x y then Srg.ReflectT else Srg.ReflectF) };
      coq_Algebra_AddMagma_isAddSemigroup_mixin =
        Srg.Algebra.AddMagma_isAddSemigroup.Axioms_;
      coq_GRing_Nmodule_isPzSemiRing_mixin =
        { Srg.GRing.Nmodule_isPzSemiRing.one = Fp.repr 1; mul = Fp.mul p };
      coq_GRing_PzSemiRing_isNonZero_mixin =
        Srg.GRing.PzSemiRing_isNonZero.Axioms_;
      coq_GRing_PzSemiRing_hasCommutativeMul_mixin =
        Srg.GRing.PzSemiRing_hasCommutativeMul.Axioms_;
      coq_GRing_NzRing_hasMulInverse_mixin =
        { Srg.GRing.NzRing_hasMulInverse.unit_subdef = (fun x -> Fp.obj x <> 0);
          inv = Fp.inv p };
      coq_GRing_UnitRing_isField_mixin = Srg.GRing.UnitRing_isField.Axioms_;
      coq_GRing_ComUnitRing_isIntegral_mixin =
        Srg.GRing.ComUnitRing_isIntegral.Axioms_;
      fintype_isFinite_mixin = List.init p Fp.repr }

let paley_matrix (p : int) : bool list list =
  let f = fp_instance p and verts = List.init p Fp.repr in
  List.map (fun u -> List.map (Srg.paley_adj f u) verts) verts


(* CLI *)

let is_prime n =
  n >= 2 &&
  (let rec aux d = d * d > n || (n mod d <> 0 && aux (d + 1)) in aux 2)

let usage () =
  Printf.eprintf "Usage: %s hamming <q>   — adjacency matrix of H(2,q)\n" Sys.argv.(0);
  Printf.eprintf "       %s paley  <p>   — adjacency matrix of Paley(p)\n" Sys.argv.(0);
  exit 1

let die fmt = Printf.ksprintf (fun s -> prerr_endline ("Error: " ^ s); exit 1) fmt

let () =
  if Array.length Sys.argv <> 3 then usage ();
  let arg = Sys.argv.(2) in
  let n = try int_of_string arg with Failure _ -> die "%s is not an integer" arg in
  match Sys.argv.(1) with
  | "hamming" ->
    if n < 2 then die "q must be >= 2";
    print_matrix (hamming_matrix n)
  | "paley" ->
    if not (is_prime n) then die "%d is not prime" n;
    if n mod 4 <> 1 then die "%d is not congruent to 1 mod 4" n;
    print_matrix (paley_matrix n)
  | _ -> usage ()
