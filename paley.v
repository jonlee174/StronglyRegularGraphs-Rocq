(*
    Paley graphs over finite fields are strongly regular.

    Authors: Ejean Kuo, Jonathan Lee
    Date: February 2026
*)

From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_field.
From GraphTheory.core Require Import edone preliminaries digraph sgraph.
Require Import main.

Import GRing.Theory.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Open Scope ring_scope.


(* Quadratic Residues *)

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
  case/andP=> _ /existsP[a /andP[Ha /eqP Heq]].
  by exists a => //; rewrite expr2.
Qed.

Lemma QR_sqr (a : F) : a != 0 -> is_QR (a ^+ 2).
Proof.
  move=> Ha; rewrite /is_QR expf_neq0 //=.
  apply/existsP; exists a; rewrite Ha /=.
  by rewrite -expr2.
Qed.

Lemma QR_mul_square (x a : F) :
  a != 0 -> is_QR x -> is_QR (a ^+ 2 * x).
Proof.
  move=> Ha /andP[Hx_neq0 /existsP[b /andP[Hb_neq0 /eqP Hb_sq]]].
  rewrite /is_QR mulf_neq0 ?expf_neq0 //=.
  apply/existsP; exists (a * b).
  rewrite mulf_neq0 //=.
  by rewrite mulrACA -[a * a]expr2 Hb_sq.
Qed.

Lemma QR_mul_square_inv (x a : F) :
  a != 0 -> is_QR (a ^+ 2 * x) -> is_QR x.
Proof.
  move=> Ha Hax.
  have Hai: a^-1 != 0 by rewrite invr_neq0.
  have := QR_mul_square (a ^+ 2 * x) (a^-1) Hai Hax.
  by rewrite exprVn mulrA mulVf ?expf_neq0 // mul1r.
Qed.

Lemma QR_neg (x : F) :
  is_QR (- (1 : F)) -> is_QR x -> is_QR (- x).
Proof.
  move=> Hneg1 /andP[Hx /existsP[b /andP[Hb /eqP Hb_sq]]].
  rewrite /is_QR oppr_eq0 Hx /=.
  move: Hneg1 => /andP[_ /existsP[c /andP[Hc /eqP Hc_sq]]].
  apply/existsP; exists (c * b).
  rewrite mulf_neq0 //=.
  by rewrite mulrACA Hc_sq Hb_sq mulN1r.
Qed.

Lemma QR_neg_iff (x : F) :
  is_QR (- (1 : F)) -> is_QR (- x) = is_QR x.
Proof.
  move=> Hneg1.
  apply/idP/idP.
  - move=> H; have := QR_neg (- x) Hneg1 H; by rewrite opprK.
  - by move=> H; exact: (QR_neg x Hneg1 H).
Qed.

End QuadraticResidues.

Arguments QR_neq0 {F x} _.
Arguments QR_has_sqrt {F x} _.
Arguments QR_sqr {F a} _.
Arguments QR_mul_square {F x a} _ _.
Arguments QR_mul_square_inv {F x a} _ _.
Arguments QR_neg {F x} _ _.
Arguments QR_neg_iff {F x} _.


(* Paley Graph *)

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
  rewrite /paley_adj eq_sym.
  case: (x =P y) => [->|Hneq] //=.
  suff H: forall a : F, is_QR F a -> is_QR F (- a).
  { case Hxy: (is_QR F (x - y)); case Hyx: (is_QR F (y - x)) => //.
    - exfalso; move: Hxy => /H; by rewrite opprB Hyx.
    - exfalso; move: Hyx => /H; by rewrite opprB Hxy. }
  move=> w; exact: (QR_neg neg1_is_square).
Qed.

Definition paley_graph : sgraph := SGraph paley_sym paley_irrefl.

Lemma paley_edgeE (x y : F) : @sedge paley_graph x y = paley_adj x y.
Proof. by []. Qed.


(* Affine Automorphisms *)

Lemma affine_preserves_adj (a b x y : F) :
  a != 0 ->
  paley_adj x y = paley_adj (a ^+ 2 * x + b) (a ^+ 2 * y + b).
Proof.
  move=> Ha.
  rewrite /paley_adj.
  have Hinj: (a ^+ 2 * x + b == a ^+ 2 * y + b) = (x == y).
  { rewrite -subr_eq0 opprD addrACA subrr addr0.
    rewrite -mulrBr mulf_eq0 expf_eq0 /=.
    by rewrite (negbTE Ha) /= subr_eq0. }
  rewrite Hinj.
  case: (x =P y) => //= Hneq.
  rewrite opprD addrACA subrr addr0 -mulrBr.
  apply/idP/idP.
  - exact: QR_mul_square.
  - exact: QR_mul_square_inv.
Qed.

Lemma affine_preserves_cn (a b x y : F) :
  a != 0 ->
  @num_common_neighbors paley_graph x y =
  @num_common_neighbors paley_graph (a ^+ 2 * x + b) (a ^+ 2 * y + b).
Proof.
  move=> Ha.
  set x' := a ^+ 2 * x + b.
  set y' := a ^+ 2 * y + b.
  set phi := fun t : F => a ^+ 2 * t + b.
  set phi_inv := fun t : F => a ^- 2 * (t - b).
  have phi_inj : injective phi.
  { move=> s t /eqP; rewrite /phi -subr_eq0 opprD addrACA subrr addr0.
    rewrite -mulrBr mulf_eq0 expf_eq0 (negbTE Ha) /= subr_eq0.
    by move/eqP. }
  have phi_inv_cancel : forall t, phi (phi_inv t) = t.
  { move=> t; rewrite /phi /phi_inv mulrA mulfV ?expf_neq0 // mul1r.
    by rewrite subrK. }
  rewrite /num_common_neighbors /common_neighbors /neighborhood.
  have ->: [set z | @sedge paley_graph x z] :&: [set z | @sedge paley_graph y z] =
           [set z : F | paley_adj x z && paley_adj y z].
  { by apply/setP => z; rewrite !inE. }
  have ->: [set z | @sedge paley_graph x' z] :&: [set z | @sedge paley_graph y' z] =
           [set z : F | paley_adj x' z && paley_adj y' z].
  { by apply/setP => z; rewrite !inE. }
  rewrite -(card_imset _ phi_inj).
  apply: eq_card => z; rewrite !inE.
  apply/imsetP/andP.
  - move=> [w]; rewrite inE => /andP[Hw1 Hw2] ->.
    by split; rewrite /x' /y' -(affine_preserves_adj a b _ w Ha).
  - move=> [Hz1 Hz2].
    exists (phi_inv z); last by rewrite -/(phi _) phi_inv_cancel.
    rewrite inE; apply/andP; split.
    + rewrite (affine_preserves_adj a b x (phi_inv z) Ha).
      by rewrite -/(phi (phi_inv z)) phi_inv_cancel -/x'.
    + rewrite (affine_preserves_adj a b y (phi_inv z) Ha).
      by rewrite -/(phi (phi_inv z)) phi_inv_cancel -/y'.
Qed.


(* Edge Transitivity *)

Lemma edge_transitive (x y : F) :
  paley_adj x y ->
  exists (a : F) (b : F), a != 0 /\
    a ^+ 2 * x + b = 0 /\ a ^+ 2 * y + b = 1.
Proof.
  rewrite /paley_adj => /andP[Hneq HQR].
  have [c Hc Hc_sq] := QR_has_sqrt HQR : exists2 a : F, a != 0 & a ^+ 2 = x - y.
  move: neg1_is_square => /andP[_ /existsP[d /andP[Hd /eqP Hd_sq]]].
  set a := d * c^-1.
  set b := - (a ^+ 2 * x).
  exists a, b.
  have Ha: a != 0 by rewrite /a mulf_neq0 // invr_neq0.
  split => //; split.
  - by rewrite /b addrN.
  - rewrite /b -mulrBr /a expr2 mulrACA.
    rewrite Hd_sq -invrM ?unitfE // -expr2 Hc_sq.
    rewrite mulN1r -[y - x]opprB mulrNN.
    by rewrite mulVf // subr_eq0.
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
  have Hxy0 : x - y != 0 by rewrite subr_eq0.
  have HnQRxy : ~~ is_QR F (x - y).
  { by move: Hnadj; rewrite /paley_adj Hneq. }
  have Hxy'0 : x' - y' != 0 by rewrite subr_eq0.
  have HnQRxy' : ~~ is_QR F (x' - y').
  { by move: Hnadj'; rewrite /paley_adj Hneq'. }
  have [a Ha Hscale] := @nonQR_coset (x - y) (x' - y') Hxy0 HnQRxy Hxy'0 HnQRxy'.
  set b := x' - a ^+ 2 * x.
  exists a, b; split => //; split.
  - by rewrite /b addrCA subrr addr0.
  - rewrite /b addrCA -mulrBr -opprB mulrN Hscale.
    by rewrite opprB addrCA subrr addr0.
Qed.


(* Degree *)

Lemma paley_degree (x : F) :
  @degree paley_graph x = q.-1./2.
Proof.
  rewrite /degree /neighborhood /= -card_QR.
  set f := fun s : F => x - s.
  have f_cancel : cancel f f.
  { by move=> s; rewrite /f opprB addrCA subrr addr0. }
  have f_inj : injective f := can_inj f_cancel.
  have Hset: [set y | @sedge paley_graph x y] = f @: [set s : F | is_QR F s].
  { apply/setP => y; rewrite inE /=.
    apply/idP/imsetP.
    - move=> Hadj.
      exists (x - y); last by rewrite /f opprB addrCA subrr addr0.
      by rewrite inE; move: Hadj; rewrite /paley_adj => /andP[].
    - move=> [s]; rewrite inE => HQRs ->.
      rewrite /paley_adj /f opprB addrCA subrr addr0 HQRs andbT.
      by rewrite -subr_eq0 opprB addrCA subrr addr0 (negbTE (QR_neq0 HQRs)). }
  by rewrite Hset card_imset.
Qed.

Lemma paley_regular : @is_regular paley_graph q.-1./2.
Proof. by move=> x; exact: paley_degree. Qed.


(* Lambda *)

Lemma zero_adj_one : @sedge paley_graph 0 1.
Proof.
  rewrite /= /paley_adj eq_sym oner_neq0 /=.
  rewrite sub0r.
  exact: neg1_is_square.
Qed.

Lemma cn_01_set :
  @common_neighbors paley_graph 0 1 =
  [set z : F | is_QR F z && is_QR F (z - 1)].
Proof.
  apply/setP => z.
  rewrite /common_neighbors /neighborhood.
  have HnegQR: forall w : F, is_QR F (- w) = is_QR F w.
  { by move=> w; rewrite (QR_neg_iff neg1_is_square). }
  apply/idP/idP.
  - move=> /setIP[]; rewrite !inE.
    change (paley_adj 0 z -> paley_adj 1 z -> is_QR F z && is_QR F (z - 1)).
    rewrite /paley_adj sub0r HnegQR -opprB HnegQR.
    by move=> /andP[_ ->] /andP[_ ->].
  - move=> Hz.
    have /andP[HQRz HQRz1] : is_QR F z && is_QR F (z - 1).
    { by move: Hz; rewrite inE. }
    rewrite inE; apply/andP; split; rewrite inE.
    + change (paley_adj 0 z).
      rewrite /paley_adj sub0r HnegQR HQRz andbT.
      by rewrite eq_sym; exact: QR_neq0 HQRz.
    + change (paley_adj 1 z).
      rewrite /paley_adj -opprB HnegQR HQRz1 andbT.
      have Hz1: z - 1 != 0 := QR_neq0 HQRz1.
      by move: Hz1; rewrite subr_eq0 => Hz1; rewrite eq_sym Hz1.
Qed.

Hypothesis lambda_count :
  #|[set z : F | is_QR F z && is_QR F (z - 1)]| = ((q - 5) %/ 4)%N.

Lemma lambda_at_01 :
  @num_common_neighbors paley_graph 0 1 = ((q - 5) %/ 4)%N.
Proof.
  by rewrite /num_common_neighbors cn_01_set lambda_count.
Qed.

Lemma lambda_uniform (x y : F) :
  @sedge paley_graph x y ->
  @num_common_neighbors paley_graph x y = ((q - 5) %/ 4)%N.
Proof.
  rewrite /= => Hadj.
  have [a [b [Ha [Hax Hay]]]] := @edge_transitive x y Hadj.
  rewrite (@affine_preserves_cn a b x y Ha).
  by rewrite Hax Hay lambda_at_01.
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
  case: (x =P y) => [->|Hneq]; first by apply: connect0.
  case Hadj: (x -- y); first by apply: connect1.
  have Hneq' : x != y by apply/eqP.
  have Hmu := @mu_uniform x y Hneq' (negbT Hadj).
  have Hmu_pos : (0 < (q - 1) %/ 4)%N.
  { have Hq1: (1 <= q)%N by apply: leq_trans (ltnW q_ge_5).
    by rewrite divn_gt0 // -(leq_add2r 1) (subnK Hq1). }
  rewrite -Hmu in Hmu_pos.
  have [z Hz] : exists z, z \in @common_neighbors paley_graph x y.
  { by apply/card_gt0P; rewrite /num_common_neighbors in Hmu_pos. }
  move: Hz; rewrite /common_neighbors /neighborhood !inE => /andP[Hxz Hyz].
  apply: (connect_trans (y := z)); first exact: connect1.
  by apply: connect1; rewrite sg_sym.
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
  have Hq : exists t, q = (4 * t + 1)%N.
  { exists (q %/ 4)%N. rewrite {1}(divn_eq q 4) q_mod4 addn1.
    by rewrite mulnC addn1. }
  destruct Hq as [t Ht].
  rewrite Ht.
  have H1 : ((4 * t + 1).-1./2 = 2 * t)%N.
  { have Hdbl : (4 * t = (2 * t).*2)%N by rewrite -addnn -mulnDl.
    by rewrite Hdbl -subn1 addnK doubleK. }
  have H2 : ((4 * t + 1 - 5) %/ 4 = t - 1)%N.
  { clear H1 Ht; case: t => [|[|t']] //.
    by rewrite mulnS -addnA addnC -addnA /= addnK mulKn. }
  have H3 : ((4 * t + 1 - 1) %/ 4 = t)%N.
  { by rewrite addnK mulKn. }
  have Ht1 : (0 < t)%N.
  { clear -Ht q_ge_5; move: q_ge_5; rewrite Ht; by case: t Ht. }
  rewrite H1 H2 H3.
  congr (SRGParams _ _ _ _).
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
  have Heven_pred : ~~ odd q.-1.
  { by rewrite -oddS prednK //; apply: ltn_trans q_ge_5. }
  apply: (@srg_complement_closure paley_graph paley_params) => //.
  - apply: leq_trans (leq_div _ 4) _.
    apply: leq_trans (leq_sub2l q (isT : (1 <= 5)%N)) _.
    by rewrite subn1 mul2n (even_halfK Heven_pred).
  - apply: leq_trans (leq_div _ 4) _.
    by rewrite subn1 mul2n (even_halfK Heven_pred).
  - by rewrite mul2n (even_halfK Heven_pred); apply: leq_pred.
  - exact: paley_is_srg.
Qed.

End PaleyGraph.