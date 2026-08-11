(*
    Paley graphs over finite fields are strongly regular.

    Authors: Ejean Kuo, Jonathan Lee
    Date: February 2026
*)

From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_field.
From mathcomp Require Import cyclic.
From GraphTheory.core Require Import edone preliminaries digraph sgraph.
Require Import main.

Import GRing.Theory FinRing.Theory.

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


(* Counting the quadratic residues *)

(* In odd characteristic 2 is invertible *)
Lemma finField_two_neq0 : odd q -> 2%:R != 0 :> F.
Proof.
  move=> oddq; apply/eqP => H2.
  have Hd : (#[(1%R : F)]%g %| 2)%N.
    by rewrite order_dvdn zmodXgE zmod1gE -[1 *+ 2]/(2%:R) H2.
  have p2 : prime 2 by [].
  have /primeP[_ /(_ _ Hd)] := p2.
  rewrite order_eq1 zmod1gE (negbTE (oner_neq0 F)) /= => /eqP Hord.
  have : (2 %| q)%N.
    by rewrite -Hord /q -cardsT; apply: order_dvdG; rewrite inE.
  by rewrite dvdn2 oddq.
Qed.

(* Every quadratic residue has exactly two square roots *)
Lemma QR_fibre_card (x : F) :
  2%:R != 0 :> F -> is_QR x ->
  #|[pred a : F | (a != 0) && (a * a == x)]| = 2.
Proof.
  move=> H2 Hx; have [b Hb Hbsq] := QR_has_sqrt x Hx.
  have Hbne : b != - b.
  { apply/eqP => Hbb.
    have : b *+ 2 = 0 by rewrite mulr2n {2}Hbb subrr.
    by rewrite -mulr_natl => /eqP; rewrite mulf_eq0 (negbTE H2) (negbTE Hb). }
  have Hset : [pred a : F | (a != 0) && (a * a == x)] =i [set b; - b].
  { move=> a; rewrite !inE /=; apply/idP/idP.
    - case/andP=> _ /eqP Ha.
      have : (a - b) * (a + b) == 0.
        by rewrite -subr_sqr expr2 Ha Hbsq subrr.
      by rewrite mulf_eq0 subr_eq0 addr_eq0 => /orP[]->; rewrite ?orbT.
    - case/orP=> /eqP ->.
      + by rewrite Hb /= -expr2 Hbsq.
      + by rewrite oppr_eq0 Hb /= mulrNN -expr2 Hbsq. }
  by rewrite (eq_card Hset) cards2 Hbne.
Qed.

(* The squaring map is 2-to-1 from F^* onto the residues, so exactly half of the nonzero elements are squares.
  (False in characteristic 2, where squaring is a bijection) *)
Lemma card_QR_odd : odd q -> #|[set x : F | is_QR x]| = q.-1./2.
Proof.
  move=> oddq; have H2 := finField_two_neq0 oddq.
  have key : (q.-1 = #|[set x : F | is_QR x]| * 2)%N.
  { rewrite -/q -(cardC1 (0 : F)) -[X in X = _]sum1_card.
    rewrite (partition_big (fun a : F => a * a) (fun x => is_QR x)) /=; last first.
      by move=> a; rewrite !inE -expr2 => Ha; exact: QR_sqr.
    rewrite -sum_nat_const.
    under [X in _ = X]eq_bigl => i do rewrite inE.
    apply: eq_bigr => x Hx; rewrite sum1_card.
    by apply: (eq_trans _ (QR_fibre_card x H2 Hx)); apply: eq_card => a; rewrite !inE. }
  by rewrite key muln2 doubleK.
Qed.

(* F^* is cyclic of order q - 1. 
  When 4 | q - 1 it contains an element h of order 4, and h^2 is then the square root of -1 *)
Lemma neg1_QR : (q %% 4 = 1)%N -> is_QR (- (1 : F)).
Proof.
  move=> q4; have q1 : (1 < q)%N by rewrite /q finNzRing_gt1.
  have H4 : (4 %| q.-1)%N by rewrite -subn1 -eqn_mod_dvd ?q4 // ltnW.
  have [k Hk] : exists k, q.-1 = (4 * k)%N.
    by exists (q.-1 %/ 4)%N; rewrite mulnC divnK.
  have qm1gt0 : (0 < q.-1)%N by rewrite -subn1 subn_gt0.
  have kgt0 : (0 < k)%N by move: qm1gt0; rewrite Hk muln_gt0 => /andP[].
  have /cyclicP[g Hg] := field_unit_group_cyclic [set: {unit F}]%G.
  have Hord : #[g]%g = q.-1 by rewrite /order -Hg card_finField_unit.
  set h := (g ^+ k)%g.
  have Hh2 : (h ^+ 2)%g != 1%g.
  { rewrite /h -expgM -order_dvdn Hord Hk; apply/negP => Hdvd.
    have := dvdn_leq _ Hdvd; rewrite muln_gt0 kgt0 /= => /(_ isT).
    by rewrite mulnC leq_pmul2l. }
  have Hfour : (h ^+ 4)%g = 1%g by rewrite /h -expgM mulnC -Hk -Hord expg_order.
  have Hsq : (\val ((h ^+ 2)%g : {unit F})) ^+ 2 = 1.
  { by rewrite -val_unitX -expgM Hfour val_unit1. }
  have Hval : (\val (h : {unit F})) ^+ 2 = - 1.
  { move: Hsq => /eqP; rewrite sqrf_eq1 => /orP[] /eqP Hv.
    - by case/negP: Hh2; apply/eqP/val_inj; rewrite Hv val_unit1.
    - by rewrite -val_unitX. }
  by rewrite -Hval; apply: QR_sqr; rewrite -unitfE (valP h).
Qed.

End QuadraticResidues.

Arguments QR_neq0 {F x} _.
Arguments QR_has_sqrt {F x} _.
Arguments QR_sqr {F a} _.
Arguments QR_mul_square {F x a} _ _.
Arguments QR_mul_square_inv {F x a} _ _.
Arguments QR_neg {F x} _ _.
Arguments QR_neg_iff {F x} _.
Arguments finField_two_neq0 {F} _.
Arguments QR_fibre_card {F} x _ _.
Arguments card_QR_odd {F} _.
Arguments neg1_QR {F} _.

Section QRCoset.

Variable F : finFieldType.
Let q := #|F|.

(* For non-square x, multiplication by x maps the squares onto the non-squares,
   so any two non-squares differ by a square factor *)
Lemma nonQR_coset_odd (x y : F) : odd q ->
  x != 0 -> ~~ is_QR F x -> y != 0 -> ~~ is_QR F y ->
  exists2 a : F, a != 0 & a ^+ 2 * x = y.
Proof.
  move=> oddq Hx HxN Hy HyN.
  pose m := q.-1./2.
  pose S := [set z : F | is_QR F z].
  pose N := [set z : F | (z != 0) && ~~ is_QR F z].
  pose A := [set: F] :\ (0 : F).
  have Hq1 : (1 < q)%N by rewrite /q finNzRing_gt1.
  have Hq0 : (0 < q)%N := ltnW Hq1.
  have Hev : ~~ odd q.-1 by rewrite -oddS prednK ?oddq.
  have Hqm : q.-1 = (m + m)%N by rewrite /m addnn even_halfK.
  have H0S : (0 : F) \notin S by rewrite inE; apply/negP=> /QR_neq0; rewrite eqxx.
  have HS : #|S| = m by exact: card_QR_odd.
  have HA : #|A| = q.-1.
  { by have := cardsD1 (0 : F) [set: F]; rewrite inE cardsT -/q add1n => ->. }
  have HAS : A :&: S = S.
  { by apply/setP=> z; rewrite !inE andbT andb_idl //; exact: QR_neq0. }
  have HAN : A :\: S = N.
  { by apply/setP=> z; rewrite !inE andbT andbC. }
  have Hsum : (#|S| + #|N|)%N = q.-1.
  { by rewrite -HA -(cardsID S A) HAS HAN. }
  have HN : #|N| = m.
  { have H := Hsum; rewrite HS Hqm in H.
    by apply/eqP; move/eqP: H; rewrite eqn_add2l. }
  have Hsub : [set x * s | s in S] \subset N.
  { apply/subsetP=> z /imsetP[s]; rewrite inE => Hs ->.
    rewrite inE mulf_neq0 ?(QR_neq0 Hs) //=.
    apply/negP=> Hxs; case/negP: HxN.
    have [a Ha Hasq] := QR_has_sqrt Hs.
    by apply: (QR_mul_square_inv Ha); rewrite Hasq mulrC. }
  have Heq : [set x * s | s in S] = N.
  { by apply/eqP; rewrite eqEcard Hsub /= card_imset ?HS ?HN //; apply: mulfI. }
  have : y \in N by rewrite inE Hy HyN.
  rewrite -Heq => /imsetP[s]; rewrite inE => Hs Hys.
  have [a Ha Hasq] := QR_has_sqrt Hs.
  by exists a => //; rewrite Hasq mulrC.
Qed.

End QRCoset.

Arguments nonQR_coset_odd {F} x y _ _ _ _ _.


Section PaleyGraph.

Variable F : finFieldType.
Let q := #|F|.

Hypothesis q_mod4 : (q %% 4 = 1)%N.

Lemma q_odd : odd q.
Proof. by rewrite {1}(divn_eq q 4) q_mod4 oddD oddM. Qed.

(* q = 1 mod 4 and q > 1 leave no room below 5 *)
Lemma q_ge_5 : (4 < q)%N.
Proof.
have q1 : (1 < q)%N by rewrite /q finNzRing_gt1.
by move: q_mod4 q1; rewrite /q; case: #|F| => [|[|[|[|[|n]]]]].
Qed.

Lemma neg1_is_square : is_QR F (- (1 : F)).
Proof. exact: neg1_QR q_mod4. Qed.

Lemma card_QR : #|[set x : F | is_QR F x]| = q.-1./2.
Proof. exact: card_QR_odd q_odd. Qed.

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


(* Non-Edge Transitivity *)

Lemma nonQR_coset (x y : F) :
  x != 0 -> ~~ is_QR F x -> y != 0 -> ~~ is_QR F y ->
  exists2 a : F, a != 0 & a ^+ 2 * x = y.
Proof. exact: nonQR_coset_odd x y q_odd. Qed.

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

(* Non-edge transitivity makes the common-neighbour count constant on non-edges *)
Lemma mu_uniform_pair (x y x' y' : F) :
  x != y -> ~~ @sedge paley_graph x y ->
  x' != y' -> ~~ @sedge paley_graph x' y' ->
  @num_common_neighbors paley_graph x y = @num_common_neighbors paley_graph x' y'.
Proof.
  rewrite /= => Hneq Hnadj Hneq' Hnadj'.
  have [a [b [Ha [Hax Hay]]]] := nonedge_transitive _ _ _ _ Hneq Hnadj Hneq' Hnadj'.
  by rewrite (affine_preserves_cn a b _ _ Ha) Hax Hay.
Qed.

(* q = 4s + 5, the shape that makes the parameter arithmetic exact *)
Lemma q_shape : exists s, q = (4 * s + 5)%N.
Proof.
  have H4 : (0 < q %/ 4)%N by rewrite divn_gt0 //; exact: ltnW q_ge_5.
  have Hd : q = (4 * (q %/ 4) + 1)%N by rewrite {1}(divn_eq q 4) q_mod4 mulnC.
  exists (q %/ 4).-1.
  by rewrite {1}Hd -{1}(prednK H4) mulnSr -addnA.
Qed.

(* The graph is not complete, so some non-edge exists *)
Lemma exists_nonedge : exists2 z : F, (0 : F) != z & ~~ @sedge paley_graph 0 z.
Proof.
  have Hsub : neighborhood paley_graph 0 \subset [set: F] :\ (0 : F).
  { apply/subsetP => z; rewrite !inE andbT /= /paley_adj.
    by case/andP=> Hne _; rewrite eq_sym. }
  have Hcard : #|[set: F] :\ (0 : F)| = q.-1.
  { by have := cardsD1 (0 : F) [set: F]; rewrite inE cardsT -/q add1n => ->. }
  have Hprop : neighborhood paley_graph 0 \proper [set: F] :\ (0 : F).
  { rewrite properEcard Hsub /= Hcard -/(degree paley_graph 0) paley_degree.
    by rewrite -divn2 ltn_Pdiv // -subn1 subn_gt0; apply: ltn_trans q_ge_5. }
  have /properP[_ [z Hz1 Hz2]] := Hprop.
  by exists z; [move: Hz1; rewrite !inE andbT eq_sym | move: Hz2; rewrite inE].
Qed.

(* Counting edges out of N(0) determines mu once lambda is known *)
Lemma mu_uniform (x y : F) :
  x != y -> ~~ @sedge paley_graph x y ->
  @num_common_neighbors paley_graph x y = ((q - 1) %/ 4)%N.
Proof.
  move=> Hne Hna.
  have [s Hq] := q_shape.
  have Hq1 : q.-1 = (4 * s + 4)%N by rewrite -subn1 Hq -addnBA.
  have H2 : ((2 * s + 2).*2 = 4 * s + 4)%N by rewrite -mul2n mulnDr mulnA.
  have H41 : (4 * s.+1 = 4 * s + 4)%N by rewrite mulnSr.
  have Hm : q.-1./2 = (2 * s + 2)%N by rewrite Hq1 -H2 doubleK.
  have Hlam : ((q - 5) %/ 4)%N = s by rewrite Hq addnK mulKn.
  have Hmu : ((q - 1) %/ 4)%N = s.+1 by rewrite Hq -addnBA // -H41 mulKn.
  have Hss : (s.+1 + s.+1 = 2 * s + 2)%N by rewrite addSn addnS addnn mul2n addn2.
  have H45 : ((2 * s + 2).+1 + (2 * s + 2) = 4 * s + 5)%N.
  { by rewrite addSn addnn H2 -addn1 -addnA. }
  have [z Hz0 Hznadj] := exists_nonedge.
  pose mu0 := @num_common_neighbors paley_graph 0 z.
  have Hall : forall u v : F, u != v -> ~~ @sedge paley_graph u v ->
              @num_common_neighbors paley_graph u v = mu0.
  { by move=> u v Hu Hv; apply: mu_uniform_pair. }
  have HU : #|neighborhood paley_graph 0 :|: [set (0 : F)]| = (2 * s + 2).+1.
  { by rewrite setUC cardsU1 not_in_neighborhood /= add1n
       -/(degree paley_graph 0) paley_degree Hm. }
  have Hcompl : #|~: (neighborhood paley_graph 0 :|: [set (0 : F)])|
              = (2 * s + 2)%N.
  { have := cardsC (neighborhood paley_graph 0 :|: [set (0 : F)]).
    by rewrite ?cardsT -/q HU Hq -H45 => /eqP; rewrite eqn_add2l => /eqP. }
  have Hpos : (0 < 2 * s + 2)%N by rewrite addnC.
  have Hcount := @srg_edge_count paley_graph q.-1./2 ((q - 5) %/ 4) mu0 0
                   paley_regular lambda_uniform Hall.
  rewrite Hcompl Hlam Hm -mulnDr in Hcount.
  move/eqP: Hcount; rewrite eqn_pmul2l // => /eqP Hcount2.
  rewrite (Hall _ _ Hne Hna) Hmu.
  by apply/eqP; move/eqP: Hcount2; rewrite -Hss eqn_add2r.
Qed.


(* Connectivity *)

Lemma paley_connected : connected [set: paley_graph].
Proof.
  apply: connectedTI => x y.
  case: (x =P y) => [->|/eqP Hneq]; first exact: connect0.
  case Hadj: (x -- y); first exact: connect1.
  have Hmu := mu_uniform _ _ Hneq (negbT Hadj).
  have Hmu_pos : (0 < (q - 1) %/ 4)%N.
  { rewrite divn_gt0 // -(leq_add2r 1) (subnK (leq_trans _ (ltnW q_ge_5))) //.
    exact: q_ge_5. }
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
  have Hep : ~~ odd q.-1 by rewrite -oddS prednK ?q_odd //; apply: ltn_trans q_ge_5.
  apply: (@srg_complement_closure paley_graph paley_params) => //.
  - by apply: leq_trans (leq_div _ 4) _;
       rewrite mul2n (even_halfK Hep) -subn1; exact: leq_sub2l.
  - by apply: leq_trans (leq_div _ 4) _; rewrite mul2n (even_halfK Hep) subn1.
  - by rewrite mul2n (even_halfK Hep); apply: leq_pred.
  - exact: paley_is_srg.
Qed.

End PaleyGraph.
