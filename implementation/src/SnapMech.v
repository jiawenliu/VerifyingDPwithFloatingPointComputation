(**
   This file contains the coq implementation of the snapping mechanism.
 **)
From Coq
     Require Import QArith.QArith QArith.Qminmax QArith.Qabs QArith.Qreals
     micromega.Psatz Reals.Reals
     Strings.Ascii Strings.BinaryString Omega
     Logic.PropExtensionality
     Logic.FunctionalExtensionality.

From Snapv
     Require Import 
     Expressions Command ExpressionTransitions
     CommandSemantics apRHL Environments.

From Snapv.lib
     Require Import MachineType.
     
Require Import Coq.Strings.Ascii Coq.Strings.BinaryString Coq.micromega.Lra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice seq.
From mathcomp Require Import ssralg ssrnum Rstruct reals.
From extructures Require Import ord fset fmap ffun.


(** Error bound validator **)

Local Import GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope aprHoare_scope.
Open Scope com_scope.

Definition Snap (a: R) (Lam: R) (B: R) (eps: R) :=
  UNIF2 (Var 2);;
  UNIF1 (Var 1);;
  Var 3 ::= CLAMP B (ROUND Lam (a + (1/eps) * (Var 2 * LN (Var 1)))).

Lemma Snap_subsub1 (a eps x y : R) :
  0 < eps ->
  (exp ((x - a) * eps) <= y) = (x <= a + eps^-1 * ln y).
Proof.
move => Heps.
by rewrite -ler_subl_addl ler_pdivl_mull // mulrC Rexp_ln_le.
Qed.

Lemma Snap_subsub2 (a eps x y : R) :
  0 < eps ->
  (y <= exp ((x - a) * eps)) = (a + eps^-1 * ln y <= x).
Proof.
move=> Heps.
by rewrite -Rln_exp_le -ler_subr_addl ler_pdivr_mull // mulrC.
Qed.

Local Notation R2 := 2%coq_R.
   
Lemma Snap_subsub3 (a Lam eps v y : R) :
  0 < eps  ->
  (exp ((v - Lam / R2 - a) * eps) <= y <= exp ((v + Lam / R2 - a) * eps)) =
  (v - Lam / R2 <= a + eps^-1 * ln y <= v + Lam / R2).
Proof.
by move=> Heps; rewrite Snap_subsub1 // Snap_subsub2.
Qed.

Lemma Snap_sub2 (a a' Lam B eps : R) :
  0 < Lam -> 0 < B -> 0 < eps ->
  a = (Rminus a' 1) ->
  (fun pm : (state * state) =>
     (forall v : R,
         exp ((v - Lam / R2 - a) * eps / F2R (pm.1 (of_nat 2)).1) <= F2R (pm.1 (of_nat 1)).1 <=
         exp ((v + Lam / R2 - a) * eps / F2R (pm.1 (of_nat 2)).1) ->
         exp ((v - Lam / R2 - a') * eps / F2R (pm.2 (of_nat 2)).1) <= F2R (pm.2 (of_nat 1)).1 <=
         exp ((v + Lam / R2 - a') * eps / F2R (pm.2 (of_nat 2)).1))  /\  F2R (pm.1 (of_nat 2)).1 = 1
        /\ 
        F2R (pm.1 (of_nat 2)).1 = F2R (pm.2 (of_nat 2)).1) ->>
   assn_sub' 3 3 (CLAMP B (ROUND Lam (a  + 1 / eps * (Var 2 * LN (Var 1)))))
                 (CLAMP B (ROUND Lam (a' + 1 / eps * (Var 2 * LN (Var 1)))))
                 (fun pm : (state * state) =>
                    forall v, F2R (pm.1 (of_nat 3)).1 = v -> F2R (pm.2 (of_nat 3)).1 = v)
  .
Proof.
  move => HLam HB Heps Hadj st1 st2 H v /=.
  rewrite !updE eqxx.
  case: H => [] /(_ v) /= H1 [] H21 H22.
  rewrite /F2R /= in H1 H21 H22 *.
  rewrite /fln /fmult /fplus /R2F -H22 H21 /=.
  rewrite -{}H22 {}H21 !divr1 !mul1r in H1 *.
  by rewrite -!clamp_eqV -!round_eqV -!Snap_subsub3.
Qed.



 (** TODO: adaopt this Lemma into the main Proof *)
Lemma Snap_sub1:
  forall a a' Lam B eps: R,
     0 < Lam -> 0 < B -> 0 < eps->
    a = (a' - 1) ->
  (fun pm : (state * state) =>
     F2R (pm.1 (of_nat 1)).1 = exp eps * F2R (pm.2 (of_nat 1)).1
  /\
  F2R (pm.1 (of_nat 2)).1 = F2R (pm.2 (of_nat 2)).1
 /\  F2R (pm.1 (of_nat 2)).1 = 1) ->>
  (fun pm : (state * state) =>
  ( forall v : R,
   exp ((v - Lam / R2 - a) * eps / F2R (pm.1 (of_nat 2)).1) <= F2R (pm.1 (of_nat 1)).1 <=
   exp ((v + Lam / R2 - a) * eps / F2R (pm.1 (of_nat 2)).1) ->
   exp ((v - Lam / R2 - a') * eps / F2R (pm.2 (of_nat 2)).1) <= F2R (pm.2 (of_nat 1)).1 <=
   exp ((v + Lam / R2 - a') * eps / F2R (pm.2 (of_nat 2)).1))  /\  F2R (pm.1 (of_nat 2)).1 = 1
  /\ 
  F2R (pm.1 (of_nat 2)).1 = F2R (pm.2 (of_nat 2)).1).

Proof.
move =>  a a' Lam B eps HLam HB Heps Hadj st1 st2 [H1 [H2 H3]].
simpl.
simpl in H1.

simpl in H2.
simpl in H3.
split; last by split.
move => v Hp.
rewrite H1 in Hp.
rewrite H3 in H2.
rewrite H3 in Hp.
rewrite Hadj opprB [1 - a']addrC !addrA mulrDl mul1r !divr1 in Hp.
rewrite (Rexp_plus ((v - Lam / R2 - a') * eps) eps) mulrC in Hp.
case/andP: Hp => Hp1 Hp2.
have Rexp_0 : 0 < exp eps by apply Rexp_ge0.
rewrite -ler_pdivl_mull // mulKr ?unitf_gt0 // in Hp1.
rewrite -!H2 !divr1 Hp1 /=.
rewrite [_ + 1]addrC mulrDl Rexp_plus mul1r in Hp2.
by rewrite -ler_pdivl_mull // mulKr ?unitf_gt0 // in Hp2.
Qed.

Lemma SnapDP:
  forall a a' Lam B eps: R,
     0 < Lam -> 0 < B -> 0 < eps->
     a = a' - 1 ->
    aprHoare_judgement ATrue (Snap a Lam B eps) (eps * (1 + (24%coq_R * (B * eta)))) (Snap a' Lam B eps)
                       (fun (pm : (state * state)) =>
                          forall v, F2R (pm.1 (of_nat 3)).1 = v -> F2R (pm.2 (of_nat 3)).1 = v)
.

Proof.
move => a a' Lam B eps  HLam HB Heps Hadj.
unfold Snap.
eapply aprHoare_seqR.
eapply aprHoare_null2.
eapply aprHoare_seqL.
  eapply aprHoare_conseqE.
  - eapply aprHoare_unif.
  - move => * //.
    exact: Snap_sub1 HLam HB Heps Hadj.
  rewrite mulrDr mulr1 -ler_subl_addl subrr.
  rewrite lt0r in Heps; case/andP: Heps => ??.
  rewrite mulr_ge0 // mulr_ge0 //.
    apply/RleP; rewrite -[0]/0%coq_R; lra.
  rewrite lt0r in HB; case/andP: HB => ??.
  rewrite mulr_ge0 // /eta -[0]/0%coq_R; apply/RleP; lra.
eapply aprHoare_conseq.
- eapply aprHoare_asgn.
- eapply Snap_sub2 => //.
- move => st1 st2 hp //.
by apply/RleP; lra.
Qed.

(*** weakest precondition formulation
for example: replace the results to be equality **)
  Close Scope aprHoare_scope.
Close Scope R_scope.
