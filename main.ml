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

(* Hamming H(2,q) - uses Demo_srg.hamming_mat, which wraps the *)
(* formally verified hamming_adj via Coq extraction. *)

let hamming_matrix q = Demo_srg.hamming_mat q


(* Paley(p) - constructs a FinRing.Field.coq_type instance for F_p   *)
(* and calls the formally verified Srg.paley_adj via Coq extraction. *)
(* Assisted by Claude Opus 4.6 *)

let fp_instance (p : int) : Srg.FinRing.Field.coq_type =
  let eq_op (x : Obj.t) (y : Obj.t) =
    (Obj.obj x : int) = (Obj.obj y : int)
  in
  let eqP (x : Obj.t) (y : Obj.t) : Srg.reflect =
    if (Obj.obj x : int) = (Obj.obj y : int)
    then Srg.ReflectT else Srg.ReflectF
  in
  let add (x : Obj.t) (y : Obj.t) : Obj.t =
    Obj.repr (((Obj.obj x : int) + (Obj.obj y : int)) mod p)
  in
  let zero : Obj.t = Obj.repr 0 in
  let opp (x : Obj.t) : Obj.t =
    Obj.repr ((p - (Obj.obj x : int)) mod p)
  in
  let one : Obj.t = Obj.repr (if p > 1 then 1 else 0) in
  let mul (x : Obj.t) (y : Obj.t) : Obj.t =
    Obj.repr (((Obj.obj x : int) * (Obj.obj y : int)) mod p)
  in
  let elems : Obj.t list = List.init p (fun i -> Obj.repr i) in
  Obj.magic
    { Srg.FinRing.Field.coq_Algebra_hasOpp_mixin = opp;
      coq_Algebra_hasZero_mixin = zero;
      coq_Algebra_hasAdd_mixin = add;
      coq_Algebra_BaseZmoduleNmodule_isZmodule_mixin =
        Srg.Algebra.BaseZmoduleNmodule_isZmodule.Axioms_;
      coq_Algebra_BaseAddUMagma_isAddUMagma_mixin =
        Srg.Algebra.BaseAddUMagma_isAddUMagma.Axioms_;
      coq_Algebra_BaseAddMagma_isAddMagma_mixin =
        Srg.Algebra.BaseAddMagma_isAddMagma.Axioms_;
      choice_hasChoice_mixin =
        Obj.magic (fun (_p : Obj.t -> bool) (_n : int) -> (None : Obj.t option));
      choice_Choice_isCountable_mixin =
        { Srg.Choice_isCountable.pickle = Obj.magic (fun (x : int) -> x);
          unpickle = Obj.magic (fun (n : int) ->
            if 0 <= n && n < p then Some (Obj.repr n) else None) };
      eqtype_hasDecEq_mixin =
        { Srg.Coq_hasDecEq.eq_op = eq_op; eqP = eqP };
      coq_Algebra_AddMagma_isAddSemigroup_mixin =
        Srg.Algebra.AddMagma_isAddSemigroup.Axioms_;
      coq_GRing_Nmodule_isPzSemiRing_mixin =
        { Srg.GRing.Nmodule_isPzSemiRing.one = one; mul = mul };
      coq_GRing_PzSemiRing_isNonZero_mixin =
        Srg.GRing.PzSemiRing_isNonZero.Axioms_;
      coq_GRing_PzSemiRing_hasCommutativeMul_mixin =
        Srg.GRing.PzSemiRing_hasCommutativeMul.Axioms_;
      coq_GRing_NzRing_hasMulInverse_mixin =
        { Srg.GRing.NzRing_hasMulInverse.unit_subdef = (fun _ -> true);
          inv = Obj.magic (fun (_x : int) -> 0) };
      coq_GRing_UnitRing_isField_mixin =
        Srg.GRing.UnitRing_isField.Axioms_;
      coq_GRing_ComUnitRing_isIntegral_mixin =
        Srg.GRing.ComUnitRing_isIntegral.Axioms_;
      fintype_isFinite_mixin = elems }

let paley_matrix (p : int) : bool list list =
  let f = fp_instance p in
  let verts = List.init p (fun i -> Obj.repr i) in
  List.map (fun u ->
    List.map (fun v -> Srg.paley_adj f u v) verts
  ) verts


(* CLI *)

let is_prime n =
  if n < 2 then false
  else let rec aux d = d * d > n || (n mod d <> 0 && aux (d + 1))
       in aux 2

let usage () =
  Printf.eprintf "Usage: %s hamming <q>   — adjacency matrix of H(2,q)\n" Sys.argv.(0);
  Printf.eprintf "       %s paley  <p>   — adjacency matrix of Paley(p)\n" Sys.argv.(0);
  exit 1

let () =
  if Array.length Sys.argv <> 3 then usage ();
  let kind = Sys.argv.(1) in
  let n = try int_of_string Sys.argv.(2)
          with Failure _ ->
            Printf.eprintf "Error: %s is not an integer\n" Sys.argv.(2);
            exit 1
  in
  match kind with
  | "hamming" ->
    if n < 2 then (Printf.eprintf "Error: q must be >= 2\n"; exit 1);
    print_matrix (hamming_matrix n)
  | "paley" ->
    if not (is_prime n) then
      (Printf.eprintf "Error: %d is not prime\n" n; exit 1);
    if n mod 4 <> 1 then
      (Printf.eprintf "Error: %d is not congruent to 1 mod 4\n" n; exit 1);
    print_matrix (paley_matrix n)
  | _ -> usage ()
