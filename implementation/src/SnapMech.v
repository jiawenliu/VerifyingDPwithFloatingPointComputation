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

Require Import Coq.Strings.Ascii Coq.Strings.BinaryString.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice seq.

From extructures Require Import ord fset fmap ffun.


(** Error bound validator **)

Open Scope R_scope.
Open Scope aprHoare_scope.

Definition Snap (a: R) (Lam: R) (B: R) (eps: R) :=
	SEQ (UNIF1 (Var 1)) 
	(SEQ (UNIF2 (Var 2)) 
		(ASGN (Var 3) 
			(Binop Clamp (Const B) 
				(Binop Round (Const Lam)
					(Binop Plus (Const a)
						(Binop Mult (Const (1/eps))
							(Binop Mult (Var 2)
								(Unop Ln (Var 1)))))))))
.

Definition eta := 0.0000000005%R.


(* Lemma SnapDP' :
  forall a a' Lam B eps: R,
    (Rplus a (Ropp a')) = 1 ->
    hoare_rule ATrue (Snap a Lam B eps) (Rmult eps (Rplus 1 (Rmult 24%R (Rmult B eta)))) (Snap a' Lam B eps)
               (fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat 3)),(m2 (of_nat 3)) with
                                  | (v1, er1),(v2, er2) =>
                                      v1 = v2
                                  end
                    end)
.

Proof.
  intros.
  unfold Snap.
(* apply H_Seq with
      (P := ATrue)  (c1 := (UNIF1 (Var 1)))
      (c2 := (SEQ (UNIF2 (Var 2))
                  (ASGN (Var 3)
                        (Binop Clamp (Const B)
                               (Binop Round (Const Lam)
                                      (Binop Plus (Const a)
                                             (Binop Mult (Const eps)
                                                    (Binop Mult (Var 2)
                                                           (Unop Ln (Var 1))))))))))
      (r1 := (Rmult eps (Rplus 1 (Rmult 24%R (Rmult B eta))))) (r2 := (0%R))
      (d1 := (UNIF1 (Var 1)))
      (d2 := (SEQ (UNIF2 (Var 2))
                  (ASGN (Var 3)
                        (Binop Clamp (Const B)
                               (Binop Round (Const Lam)
                                      (Binop Plus (Const a')
                                             (Binop Mult (Const eps)
                                                    (Binop Mult (Var 2)
                                                           (Unop Ln (Var 1))))))))))
      (R0 :=  (fun pm : state * state =>
                 let (m1, m2) := pm in
                 let (v1, _) := m1 (of_nat 3) in
                 let (v2, _) := m2 (of_nat 3) in v1 = v2)
      ).

 *)

Admitted.
*)

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
                (v, (er1, er2)) ->
     let (v1, _) := m (of_nat 1) in
     let (s, _) := m (of_nat 2) in
     (exp ((v - Lam/2 - a) / eps / s) < v1) /\
     (v1 < exp ((v + Lam/2 - a) / eps / s)).
Proof.

  intros.
  
Admitted.

                   
         
(*functional extensionality, propositional extensionality *)
Lemma Snap_sub3:
  forall a a' Lam B eps: R,
     Rlt 0 Lam -> Rlt 0 B -> Rlt 0 eps->
    (Rminus a a') = 1 ->
  assn_sub (3%nat) (3%nat)
           (Binop Clamp 
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
           (Binop Clamp 
                  (Const B)
                  (Binop Round 
                         (Const Lam)
                         (Binop Plus 
                                (Const a')
                                (Binop Mult 
                                       (Const (1 / eps))
                                       (Binop Mult 
                                              (Var 2) 
                                              (Unop Ln (Var 1)))))))
           (fun pm : ffun (fun=> (0, (0, 0))) * ffun (fun=> (0, (0, 0))) =>
              let (m1, m2) := pm in
              let (v1, _) := m1 (of_nat 3) in
              let (v2, _) := m2 (of_nat 3) in forall v : R_eqType, v1 = v -> v2 = v)
  =
  (fun (pm : (state * state)) =>
                                  let (m1, m2) := pm in
                                  let (v1, _) := m1 (of_nat 1) in
                                  let (v2, _) := m2 (of_nat 1) in
                                  let (s1, _) := m1 (of_nat 2) in
                                  let (s2, _) := m2 (of_nat 2) in
                                  forall v,
                                   (exp ((v - Lam/2 - a) / eps / s1) < v1) /\
                                   (v1 < exp ((v + Lam/2 - a) / eps / s1))
                                    ->
                                    (Rlt (Rmult (eps) (exp (Rdiv (Rdiv (Rminus (Rminus v Lam/2) a') eps) s2))) v2 /\
                                    (Rlt v2 (Rmult (eps) (exp (Rdiv (Rdiv (Rminus (Rminus v Lam/2) a') eps) s2)))))).
Proof.
  intros.
  unfold assn_sub.
  apply functional_extensionality.
  intros.

  apply propositional_extensionality.
  split.
  intros.
  

  (*rewrite updE in H3.
  generalize v.
  apply Snap_sub1 with  (Lam := Lam) (a := a) (eps := eps) .
  rewrite <- Snap_sub1 with  (Lam := Lam) (a := a) (eps := eps) .
  *)
  admit.  

  intros.
  


Admitted.

Lemma zero_lt_eta : Rlt 0 eta.
Proof.
  unfold eta.
  lra.

Qed.




Lemma zero_lt_24 : Rlt 0 24.
Proof.
 lra.

Qed.



  

Ltac apply_snap_sub3 := apply Snap_sub3.

(* Point wise equal in terms of memeory*)
Lemma SnapDP:
  forall a a' Lam B eps: R,
     Rlt 0 Lam -> Rlt 0 B -> Rlt 0 eps->
    (Rminus a a') = 1 ->
    aprHore_judgement ATrue (Snap a Lam B eps) (Rmult eps (Rplus 1 (Rmult 24%R (Rmult B eta)))) (Snap a' Lam B eps)
               (fun (pm : (state * state)) =>
                    let (m1, m2) := pm in
                    let (v1, _) := m1 (of_nat 3) in let (v2, _) := m2 (of_nat 3) in
                                                    forall v, v1 = v -> v2 = v)
.

Proof.
  intros.
  unfold Snap.
  eapply aprHore_seq.
(* weakest precondition calculus , *)  
apply aprHore_seq with (Q := fun pm : ffun (fun=> (0, (0, 0))) * ffun (fun=> (0, (0, 0))) =>
    let (m1, m2) := pm in
    let (v1, _) := m1 (of_nat 3) in let (v2, _) := m2 (of_nat 3) in forall v, v1 = v -> v2 = v)
                       (r1 := (Rmult eps (Rplus 1 (Rmult 24%R (Rmult B eta)))) )
                       (r2 := 0%R)
                       (R0 := (fun (pm : (state * state)) =>
                                  let (m1, m2) := pm in
                                  let (v1, _) := m1 (of_nat 1) in
                                  let (v2, _) := m2 (of_nat 1) in
                                  let (s1, _) := m1 (of_nat 2) in
                                  let (s2, _) := m2 (of_nat 2) in
                                  forall v,
                                    (Rlt (exp (Rdiv (Rdiv (Rminus (Rminus v Lam/2) a) eps) s1)) v1 /\
                                     Rlt v1 (exp (Rdiv (Rdiv (Rminus (Rplus v Lam/2) a) eps) s1)))
                                    ->
                                    (Rlt (Rmult (eps) (exp (Rdiv (Rdiv (Rminus (Rminus v Lam/2) a') eps) s2))) v2 /\
                                    (Rlt v2 (Rmult (eps) (exp (Rdiv (Rdiv (Rminus (Rminus v Lam/2) a') eps) s2))))))).


apply 
 aprHore_conseq with (P' := ATrue)
                     (r' := (eps))
                     (Q' :=  (fun (pm : (state * state)) =>
                                  let (m1, m2) := pm in
                                  let (v1, _) := m1 (of_nat 1) in
                                  let (v2, _) := m2 (of_nat 1) in
                                  let (s1, _) := m1 (of_nat 2) in
                                  let (s2, _) := m2 (of_nat 2) in
                                  forall v,
                                    (Rlt (exp (Rdiv (Rdiv (Rminus (Rminus v Lam/2) a) eps) s1)) v1 /\
                                     Rlt v1 (exp (Rdiv (Rdiv (Rminus (Rplus v Lam/2) a) eps) s1)))
                                    ->
                                    (Rlt (Rmult (eps) (exp (Rdiv (Rdiv (Rminus (Rminus v Lam/2) a') eps) s2))) v2 /\
                                    (Rlt v2 (Rmult (eps) (exp (Rdiv (Rdiv (Rminus (Rminus v Lam/2) a') eps) s2)))))))
                     
.

apply aprHore_unifP with (eps :=  (eps)).


unfold assert_implies.
auto.

unfold assert_implies.
auto.
rewrite Rmult_plus_distr_l.

rewrite Rmult_comm .
rewrite  Rmult_1_l.
(assert (eps = eps + 0)).
rewrite  Rplus_0_r; auto.
rewrite H3.
rewrite Rplus_assoc.

apply  Rplus_le_compat_l .

apply Rplus_le_le_0_compat.
apply Rle_refl.
apply Rlt_le.
apply Rmult_lt_0_compat .
rewrite <- H3.
apply H1.
apply Rmult_lt_0_compat .
apply  zero_lt_24.
apply Rmult_lt_0_compat .
apply H0.
unfold eta; lra.

apply
  aprHore_seq with (Q := fun pm : ffun (fun=> (0, (0, 0))) * ffun (fun=> (0, (0, 0))) =>
    let (m1, m2) := pm in
    let (v1, _) := m1 (of_nat 3) in let (v2, _) := m2 (of_nat 3) in forall v, v1 = v -> v2 = v)
                       (r1 := 0 )
                       (r2 := 0 )
                       (R0 := (fun (pm : (state * state)) =>
                                  let (m1, m2) := pm in
                                  let (v1, _) := m1 (of_nat 1) in
                                  let (v2, _) := m2 (of_nat 1) in
                                  let (s1, _) := m1 (of_nat 2) in
                                  let (s2, _) := m2 (of_nat 2) in
                                  forall v,
                                    (Rlt (exp (Rdiv (Rdiv (Rminus (Rminus v Lam/2) a) eps) s1)) v1 /\
                                     Rlt v1 (exp (Rdiv (Rdiv (Rminus (Rplus v Lam/2) a) eps) s1)))
                                    ->
                                    (Rlt (Rmult (eps) (exp (Rdiv (Rdiv (Rminus (Rminus v Lam/2) a') eps) s2))) v2 /\
                                    (Rlt v2 (Rmult (eps) (exp (Rdiv (Rdiv (Rminus (Rminus v Lam/2) a') eps) s2))))))).
apply aprHore_conseq with
    (P' := ATrue)
    (Q' := (fun (pm : (state * state)) =>
                                  let (m1, m2) := pm in
                                  let (v1, _) := m1 (of_nat 1) in
                                  let (v2, _) := m2 (of_nat 1) in
                                  let (s1, _) := m1 (of_nat 2) in
                                  let (s2, _) := m2 (of_nat 2) in
                                  forall v,
                                    (Rlt (exp (Rdiv (Rdiv (Rminus (Rminus v Lam/2) a) eps) s1)) v1 /\
                                     Rlt v1 (exp (Rdiv (Rdiv (Rminus (Rplus v Lam/2) a) eps) s1)))
                                    ->
                                    (Rlt (Rmult (eps) (exp (Rdiv (Rdiv (Rminus (Rminus v Lam/2) a') eps) s2))) v2 /\
                                    (Rlt v2 (Rmult (eps) (exp (Rdiv (Rdiv (Rminus (Rminus v Lam/2) a') eps) s2)))))))
    (r' := 0).

apply aprHore_nulls.
unfold ATrue.
unfold assert_implies; auto.

unfold assert_implies; auto.
apply Rle_refl.

rewrite <- Snap_sub3 with (B := B).
apply aprHore_asgn with (e1 := 
                           (Binop Clamp 
                                  (Const B)
                                  (Binop Round 
                                         (Const Lam)
                                         (Binop Plus 
                                                (Const a)
                                                (Binop Mult 
                                                       (Const (1 / eps))
                                                       (Binop Mult 
                                                              (Var 2) 
                                                              (Unop Ln (Var 1))))))))
                        (e2 := 
                           (Binop Clamp (Const B)
                                  (Binop Round (Const Lam)
                                         (Binop Plus (Const a')
                                                (Binop Mult (Const (1 / eps)) (Binop Mult (Var 2) (Unop Ln (Var 1))))))))
                        (x1 := 3%nat) (x2 := 3%nat)
(Q := fun pm : ffun (fun=> (0, (0, 0))) * ffun (fun=> (0, (0, 0))) =>
    let (m1, m2) := pm in
    let (v1, _) := m1 (of_nat 3) in
    let (v2, _) := m2 (of_nat 3) in forall v : R_eqType, v1 = v -> v2 = v)
.
auto.
auto.
auto.
auto.
Qed.

Close Scope aprHoare_scope.
Close Scope R_scope.
