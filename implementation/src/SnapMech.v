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

From extructures Require Import ord fset fmap ffun.


(** Error bound validator **)

Open Scope R_scope.
Open Scope aprHoare_scope.

Definition Snap (a: R) (Lam: R) (B: R) (eps: R) :=
	SEQ (UNIF2 (Var 2)) 
	(SEQ (UNIF1 (Var 1)) 
		(ASGN (Var 3) 
			(Binop Clamp (Const B) 
				(Binop Round (Const Lam)
					(Binop Plus (Const a)
						(Binop Mult (Const (1/eps))
							(Binop Mult (Var 2)
								(Unop Ln (Var 1)))))))))
.


(* 
Lemma Snap_sub1:
  forall (a Lam B eps v er1 er2: R) m,
     Rlt 0 Lam -> Rlt 0 B -> Rlt 0 eps->
   
     trans_expr eta m (Binop Clamp 
                             (Const B)
                             (Binop Round 
                                    (Const Lam)
                                    (Binop Plus 
                                           (Const a)
                                           (Binop Mult 
                                                  (Const (1 / eps))
                                                  (Binop Mult 
                                                         (Var 2) 
                                                         (Unop Ln (Var 1)))))))
                ((F2R v), (er1, er2)) ->
     let (v1, _) := m (of_nat 1) in
     let (s, _) := m (of_nat 2) in
     (exp ((v - Lam/2 - a) / eps / s) < v1) /\
     (v1 < exp ((v + Lam/2 - a) / eps / s)).
Proof.

  intros.
  
Admitted.
*)
                   
         
(* functional extensionality, propositional extensionality *)
Lemma Snap_sub1:
  forall a a' Lam B eps: R,
     Rlt 0 Lam -> Rlt 0 B -> Rlt 0 eps->
    (Rminus a a') = 1 ->
  (fun pm : (state * state) =>
  let (m1, m2) := pm in
   let (v1, _) := m1 (of_nat 1) in
   let (v2, _) := m2 (of_nat 1) in
   forall l r : R, l <= apRHL.F2R v1 <= r -> eps * l <= apRHL.F2R v2 <= eps * r) ->>
  (fun pm : (state * state) =>
   let (m1, m2) := pm in
   let (v1, _) := m1 (of_nat 1) in
   let (v2, _) := m2 (of_nat 1) in
   let (s1, _) := m1 (of_nat 2) in
   let (s2, _) := m2 (of_nat 2) in
   forall v : R,
   exp (((v - Lam) / 2 - a) / eps / F2R s1) <= F2R v1 <=
   exp (((v + Lam) / 2 - a) / eps / F2R s1) ->
   eps * exp (((v - Lam) / 2 - a') / eps / F2R s2) <= F2R v2 <=
   eps * exp (((v - Lam) / 2 - a') / eps / F2R s2)).

Proof.



Admitted.

Lemma Snap_sub2:
  forall a a' Lam B eps: R,
     Rlt 0 Lam -> Rlt 0 B -> Rlt 0 eps->
    (Rminus a a') = 1 ->
  assn_sub' 3 3 (Binop Clamp (Const B) 
				(Binop Round (Const Lam)
					(Binop Plus (Const a)
						(Binop Mult (Const (1/eps))
							(Binop Mult (Var 2)
							       (Unop Ln (Var 1)))))))
            (Binop Clamp (Const B) 
				(Binop Round (Const Lam)
					(Binop Plus (Const a')
						(Binop Mult (Const (1/eps))
							(Binop Mult (Var 2)
							       (Unop Ln (Var 1)))))))
            (fun pm : (state * state) =>
               forall v : F_eqType, (pm.1 (of_nat 3)).1 = v -> (pm.2 (of_nat 3)).1 = v)
            = 
   (fun pm : (state * state) =>
   let (m1, m2) := pm in
   let (v1, _) := m1 (of_nat 1) in
   let (v2, _) := m2 (of_nat 1) in
   let (s1, _) := m1 (of_nat 2) in
   let (s2, _) := m2 (of_nat 2) in
   forall v : R,
   exp (((v - Lam) / 2 - a) / eps / F2R s1) <= F2R v1 <=
   exp (((v + Lam) / 2 - a) / eps / F2R s1) ->
   eps * exp (((v - Lam) / 2 - a') / eps / F2R s2) <= F2R v2 <=
   eps * exp (((v - Lam) / 2 - a') / eps / F2R s2)).
Proof.
Admitted.

Ltac apply_snap_sub1 := apply Snap_sub1.


Lemma SnapDP:
  forall a a' Lam B eps: R,
     Rlt 0 Lam -> Rlt 0 B -> Rlt 0 eps->
    (Rminus a a') = 1 ->
    aprHoare_judgement ATrue (Snap a Lam B eps) (Rmult eps (Rplus 1 (Rmult 24%R (Rmult B eta)))) (Snap a' Lam B eps)
                       (fun (pm : (state * state)) =>
                          forall v, (pm.1 (of_nat 3)).1 = v -> (pm.2 (of_nat 3)).1 = v)
.

Proof.
  move => a a' Lam B eps  HLam HB Heps Hadj.
  rewrite <- (Rplus_0_l (eps * (1 + 24 * (B * eta)))).
  unfold Snap.
  eapply aprHoare_seq.
  eapply aprHoare_null2.
  rewrite <- (Rplus_0_r (eps * (1 + 24 * (B * eta)))).
  eapply aprHoare_seq.
  eapply aprHoare_conseq.
  eapply aprHoare_unifP.
  move => * //.
  instantiate (2 := eps).
  instantiate
    (1 := (fun pm : (state * state) =>
              let (m1, m2) := pm in
              let (v1, _) := m1 (of_nat 1) in
              let (v2, _) := m2 (of_nat 1) in
              let (s1, _) := m1 (of_nat 2) in
              let (s2, _) := m2 (of_nat 2) in
              forall v : R,
                exp (((v - Lam) / 2 - a) / eps / F2R s1) <= F2R v1 <=
                exp (((v + Lam) / 2 - a) / eps / F2R s1) ->
                eps * exp (((v - Lam) / 2 - a') / eps / F2R s2) <= F2R v2 <=
                eps * exp (((v - Lam) / 2 - a') / eps / F2R s2))).

  by apply Snap_sub1 with (B := B).
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_comm .
  rewrite  Rmult_1_l.
  rewrite - {1}(Rplus_0_r eps).
  rewrite <- Rle_rle.
  apply  Rplus_le_compat_l .
  apply Rlt_le.
  apply Rmult_lt_0_compat .
  assumption.
  apply Rmult_lt_0_compat .
  lra.
  apply Rmult_lt_0_compat .
  assumption.
  unfold eta.
  lra.
  rewrite <- (Snap_sub2  a a' Lam B eps).
  by apply aprHoare_asgn; assumption.
  assumption.
  assumption.
  assumption.
  assumption. 
Qed.


  Close Scope aprHoare_scope.
Close Scope R_scope.
