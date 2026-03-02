(*
    Paley graphs over finite fields are strongly regular.

    Authors: Ejean Kuo, Jonathan Lee
    Date: February 2026
*)

From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_field.
From mathcomp Require Import cyclic.
From GraphTheory.core Require Import edone preliminaries digraph sgraph.
Require Import main.

Import GRing.Theory.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Open Scope ring_scope.


Section QuadraticResidues.

Variable F : finFieldType.
Let q := #|F|.

Definition is_QR (x : F) : bool :=
  (x != 0) && [exists a : F, (a != 0) && (a * a == x)].

Lemma QR_neq0 (x : F) : is_QR x -> x != 0.
Proof. by case/andP. Qed.

Lemma QR_has_sqrt (x : F) :
  is_QR x -> exists2 a : F, a != 0 & a ^+ 2 = x.
Proof.
  by case/andP=> _ /existsP[a /andP[Ha /eqP <-]]; exists a => //; rewrite expr2.
Qed.

Lemma QR_sqr (a : F) : a != 0 -> is_QR (a ^+ 2).
Proof.
  move=> Ha; rewrite /is_QR expf_neq0 //=.
  by apply/existsP; exists a; rewrite Ha /= -expr2.
Qed.

Lemma QR_mul_square (x a : F) :
  a != 0 -> is_QR x -> is_QR (a ^+ 2 * x).
Proof.
  move=> Ha /andP[Hx /existsP[b /andP[Hb /eqP Hb_sq]]].
  rewrite /is_QR mulf_neq0 ?expf_neq0 //=.
  by apply/existsP; exists (a * b); rewrite mulf_neq0 //= mulrACA -[a * a]expr2 Hb_sq.
Qed.

Lemma QR_mul_square_inv (x a : F) :
  a != 0 -> is_QR (a ^+ 2 * x) -> is_QR x.
Proof.
  move=> Ha Hax; have := QR_mul_square _ _ (invr_neq0 Ha) Hax.
  by rewrite exprVn mulrA mulVf ?expf_neq0 // mul1r.
Qed.

Lemma QR_neg (x : F) :
  is_QR (- (1 : F)) -> is_QR x -> is_QR (- x).
Proof.
  move=> /andP[_ /existsP[c /andP[Hc /eqP Hc_sq]]] /andP[Hx /existsP[b /andP[Hb /eqP Hb_sq]]].
  rewrite /is_QR oppr_eq0 Hx /=.
  by apply/existsP; exists (c * b); rewrite mulf_neq0 //= mulrACA Hc_sq Hb_sq mulN1r.
Qed.

Lemma QR_neg_iff (x : F) :
  is_QR (- (1 : F)) -> is_QR (- x) = is_QR x.
Proof.
  move=> Hn1; apply/idP/idP => H.
  - by have := QR_neg _ Hn1 H; rewrite opprK.
  - exact: QR_neg _ Hn1 H.
Qed.

End QuadraticResidues.

Arguments QR_neq0 {F x} _.
Arguments QR_has_sqrt {F x} _.
Arguments QR_sqr {F a} _.
Arguments QR_mul_square {F x a} _ _.
Arguments QR_mul_square_inv {F x a} _ _.
Arguments QR_neg {F x} _ _.
Arguments QR_neg_iff {F x} _.


Section PaleyGraph.

Variable F : finFieldType.
Let q := #|F|.

Hypothesis neg1_is_square : is_QR F (- (1 : F)).
Hypothesis card_QR : #|[set x : F | is_QR F x]| = q.-1./2.

Definition paley_adj (x y : F) : bool :=
  (x != y) && is_QR F (x - y).

Lemma paley_irrefl (x : F) : paley_adj x x = false.
Proof. by rewrite /paley_adj eq_refl. Qed.

Lemma paley_sym (x y : F) : paley_adj x y = paley_adj y x.
Proof.
  rewrite /paley_adj eq_sym; case: (x =P y) => [->|_] //=.
  suff H : forall u v : F, is_QR F (u - v) = is_QR F (v - u) by rewrite H.
  by move=> u v; apply/idP/idP => Huv; have := QR_neg neg1_is_square Huv; rewrite opprB.
Qed.

Definition paley_graph : sgraph := SGraph paley_sym paley_irrefl.


(* Affine Automorphisms *)

Lemma affine_preserves_adj (a b x y : F) :
  a != 0 -> paley_adj x y = paley_adj (a ^+ 2 * x + b) (a ^+ 2 * y + b).
Proof.
  move=> Ha; rewrite /paley_adj.
  have ->: (a ^+ 2 * x + b == a ^+ 2 * y + b) = (x == y).
  { by rewrite -subr_eq0 opprD addrACA subrr addr0 -mulrBr
       mulf_eq0 expf_eq0 /= (negbTE Ha) /= subr_eq0. }
  case: (x =P y) => //= _; rewrite opprD addrACA subrr addr0 -mulrBr.
  by apply/idP/idP; [exact: QR_mul_square | exact: QR_mul_square_inv].
Qed.

Lemma affine_preserves_cn (a b x y : F) :
  a != 0 ->
  @num_common_neighbors paley_graph x y =
  @num_common_neighbors paley_graph (a ^+ 2 * x + b) (a ^+ 2 * y + b).
Proof.
  move=> Ha.
  set phi := fun t : F => a ^+ 2 * t + b.
  have phi_inj : injective phi.
  { move=> s t /eqP; rewrite /phi -subr_eq0 opprD addrACA subrr addr0 -mulrBr.
    by rewrite mulf_eq0 expf_eq0 (negbTE Ha) /= subr_eq0 => /eqP. }
  have phiK t : a ^+ 2 * (a ^- 2 * (t - b)) + b = t.
  { by rewrite mulrA mulfV ?expf_neq0 // mul1r subrK. }
  rewrite /num_common_neighbors.
  have eq_cn u v : @common_neighbors paley_graph u v = [set z : F | paley_adj u z && paley_adj v z]
    by apply/setP => ?; rewrite /common_neighbors /neighborhood !inE.
  rewrite !eq_cn -(card_imset _ phi_inj); apply: eq_card => z; rewrite !inE.
  apply/imsetP/andP.
  - move=> [w]; rewrite inE => /andP[Hw1 Hw2] ->.
    by split; rewrite -(affine_preserves_adj a b _ w Ha).
  - move=> [Hz1 Hz2]; exists (a ^- 2 * (z - b)).
    + rewrite inE; apply/andP; split;
        by rewrite (affine_preserves_adj a b _ _ Ha) phiK.
    + by rewrite /phi phiK.
Qed.


(* Edge Transitivity *)

Lemma edge_transitive (x y : F) :
  paley_adj x y ->
  exists (a : F) (b : F), a != 0 /\
    a ^+ 2 * x + b = 0 /\ a ^+ 2 * y + b = 1.
Proof.
  rewrite /paley_adj => /andP[_ HQR].
  have [c Hc Hc_sq] := QR_has_sqrt HQR.
  have Hne : x - y != 0 by exact: QR_neq0 HQR.
  move: neg1_is_square => /andP[_ /existsP[d /andP[Hd /eqP Hd_sq]]].
  set a := d * c^-1; set b := - (a ^+ 2 * x).
  exists a, b; split; first by rewrite mulf_neq0 // invr_neq0.
  split; first by rewrite /b addrN.
  rewrite /b -mulrBr /a expr2 mulrACA Hd_sq -invrM ?unitfE // -expr2 Hc_sq.
  by rewrite -[y - x]opprB mulrN mulfVK ?unitfE // opprK.
Qed.


(* Non-Edge Transitivity *)

Hypothesis nonQR_coset : forall x y : F,
  x != 0 -> ~~ is_QR F x -> y != 0 -> ~~ is_QR F y ->
  exists2 a : F, a != 0 & a ^+ 2 * x = y.

Lemma nonedge_transitive (x y x' y' : F) :
  x != y -> ~~ paley_adj x y ->
  x' != y' -> ~~ paley_adj x' y' ->
  exists (a : F) (b : F), a != 0 /\
    a ^+ 2 * x + b = x' /\ a ^+ 2 * y + b = y'.
Proof.
  move=> Hneq Hnadj Hneq' Hnadj'.
  have HnQR : ~~ is_QR F (x - y) by move: Hnadj; rewrite /paley_adj Hneq.
  have HnQR' : ~~ is_QR F (x' - y') by move: Hnadj'; rewrite /paley_adj Hneq'.
  have Hxy0 : x - y != 0 by rewrite subr_eq0.
  have Hxy'0 : x' - y' != 0 by rewrite subr_eq0.
  have [a Ha Hsc] := nonQR_coset _ _ Hxy0 HnQR Hxy'0 HnQR'.
  set b := x' - a ^+ 2 * x; exists a, b; split => //; split.
  - by rewrite /b addrCA subrr addr0.
  - by rewrite /b addrCA -mulrBr -opprB mulrN Hsc opprB addrCA subrr addr0.
Qed.


(* Degree *)

Lemma paley_degree (x : F) :
  @degree paley_graph x = q.-1./2.
Proof.
  rewrite /degree /neighborhood /= -card_QR.
  set f := fun s : F => x - s.
  have f_can : cancel f f by move=> s; rewrite /f opprB addrCA subrr addr0.
  have Hset: [set y | @sedge paley_graph x y] = f @: [set s : F | is_QR F s].
  { apply/setP => y; rewrite inE /=; apply/idP/imsetP.
    - move=> Hadj; exists (x - y).
      + by rewrite inE; move: Hadj; rewrite /paley_adj => /andP[].
      + by rewrite /f opprB addrCA subrr addr0.
    - move=> [s]; rewrite inE => HQRs ->.
      rewrite /paley_adj /f opprB addrCA subrr addr0 HQRs andbT.
      by rewrite -subr_eq0 opprB addrCA subrr addr0 (negbTE (QR_neq0 HQRs)). }
  by rewrite Hset card_imset //; exact: can_inj f_can.
Qed.

Lemma paley_regular : @is_regular paley_graph q.-1./2.
Proof. by move=> x; exact: paley_degree. Qed.


(* Lambda *)

Lemma zero_adj_one : @sedge paley_graph 0 1.
Proof. by rewrite /= /paley_adj eq_sym oner_neq0 /= sub0r neg1_is_square. Qed.

Lemma cn_01_set :
  @common_neighbors paley_graph 0 1 =
  [set z : F | is_QR F z && is_QR F (z - 1)].
Proof.
  apply/setP => z; rewrite /common_neighbors /neighborhood !inE /edge_rel /= /paley_adj /=.
  rewrite sub0r (QR_neg_iff neg1_is_square) -opprB (QR_neg_iff neg1_is_square).
  case Hz: (is_QR F z); case Hz1: (is_QR F (z - 1)); rewrite ?(andbT, andbF) //=.
  rewrite eq_sym (negbTE (QR_neq0 Hz)) /=.
  by move: (QR_neq0 Hz1); rewrite subr_eq0 eq_sym => ->.
Qed.

Hypothesis lambda_count :
  #|[set z : F | is_QR F z && is_QR F (z - 1)]| = ((q - 5) %/ 4)%N.

Lemma lambda_at_01 :
  @num_common_neighbors paley_graph 0 1 = ((q - 5) %/ 4)%N.
Proof. by rewrite /num_common_neighbors cn_01_set lambda_count. Qed.

Lemma lambda_uniform (x y : F) :
  @sedge paley_graph x y ->
  @num_common_neighbors paley_graph x y = ((q - 5) %/ 4)%N.
Proof.
  rewrite /= => Hadj.
  have [a [b [Ha [Hax Hay]]]] := edge_transitive _ _ Hadj.
  by rewrite (affine_preserves_cn a b _ _ Ha) Hax Hay lambda_at_01.
Qed.


(* Mu *)

Hypothesis mu_uniform : forall x y : F,
  x != y -> ~~ @sedge paley_graph x y ->
  @num_common_neighbors paley_graph x y = ((q - 1) %/ 4)%N.


(* Connectivity *)

Hypothesis q_ge_5 : (4 < q)%N.

Lemma paley_connected : connected [set: paley_graph].
Proof.
  apply: connectedTI => x y.
  case: (x =P y) => [->|/eqP Hneq]; first exact: connect0.
  case Hadj: (x -- y); first exact: connect1.
  have Hmu := mu_uniform _ _ Hneq (negbT Hadj).
  have Hmu_pos : (0 < (q - 1) %/ 4)%N.
  { by rewrite divn_gt0 // -(leq_add2r 1) (subnK (leq_trans _ (ltnW q_ge_5))). }
  have [z Hz] : exists z, z \in @common_neighbors paley_graph x y.
  { by apply/card_gt0P; rewrite -/(num_common_neighbors _ _ _) Hmu. }
  move: Hz; rewrite /common_neighbors /neighborhood !inE => /andP[Hxz Hyz].
  apply: connect_trans (connect1 Hxz) _; by apply: connect1; rewrite sg_sym.
Qed.


Definition paley_params : srg_params :=
  SRGParams q q.-1./2 (((q - 5) %/ 4)%N) (((q - 1) %/ 4)%N).

Theorem paley_is_srg : is_srg paley_graph paley_params.
Proof.
  rewrite /is_srg /paley_params /=; split.
  - by rewrite cardsT.
  - exact: paley_connected.
  - exact: paley_regular.
  - exact: lambda_uniform.
  - exact: mu_uniform.
Qed.


(* Complement *)

Hypothesis q_mod4 : (q %% 4 = 1)%N.

Lemma paley_compl_params :
  compl_srg_params paley_params = paley_params.
Proof.
  rewrite /compl_srg_params /paley_params /=.
  have [t Ht] : exists t, q = (4 * t + 1)%N.
  { by exists (q %/ 4)%N; rewrite {1}(divn_eq q 4) q_mod4 mulnC !addn1. }
  rewrite Ht.
  have H2 : ((4 * t + 1 - 5) %/ 4 = t - 1)%N.
  { by case: t Ht => [|[|t']] // _; rewrite mulnS -addnA addnC -addnA /= addnK mulKn. }
  have H3 : ((4 * t + 1 - 1) %/ 4 = t)%N by rewrite addnK mulKn.
  have Ht1 : (0 < t)%N by move: q_ge_5 H2 H3; rewrite Ht; case: t Ht.
  have H1 : ((4 * t + 1).-1./2 = 2 * t)%N.
  { by rewrite addn1 /= -[4%N]/(2*2)%N -mulnA mul2n doubleK. }
  rewrite H1 H2 H3; congr (SRGParams _ _ _ _).
  - by rewrite -subnDA subnDr -mulnBl.
  - by rewrite mulnA /= addKn.
  - by rewrite mulnA /= addKn addnC subnK.
Qed.

Theorem paley_compl_is_srg :
  connected [set: compl paley_graph] ->
  is_srg (compl paley_graph) (compl_srg_params paley_params).
Proof.
  move=> Hconn.
  have Hodd : odd q by rewrite (divn_eq q 4) q_mod4 oddD oddM.
  have Hep : ~~ odd q.-1 by rewrite -oddS prednK //; apply: ltn_trans q_ge_5.
  apply: (@srg_complement_closure paley_graph paley_params) => //.
  - by apply: leq_trans (leq_div _ 4) _;
       rewrite mul2n (even_halfK Hep) -subn1; exact: leq_sub2l.
  - by apply: leq_trans (leq_div _ 4) _; rewrite mul2n (even_halfK Hep) subn1.
  - by rewrite mul2n (even_halfK Hep); apply: leq_pred.
  - exact: paley_is_srg.
Qed.

End PaleyGraph.
