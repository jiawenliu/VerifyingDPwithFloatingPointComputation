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
              
Axiom Rplus_minusopp : forall a b, a - b = a + (-b).
Axiom Rexp_plus : forall a b, exp (a + b) = (exp a) * (exp b).
Axiom Rmult_div : forall a b, a / b = a * / b.
Axiom Rexp_ge0 : forall r, 0 < exp r .
(* functional extensionality, propositional extensionality *)
(** TODO: adaopt this Lemma into the main Proof *)
Lemma Snap_sub1:
  forall a a' Lam B eps: R,
     Rlt 0 Lam -> Rlt 0 B -> Rlt 0 eps->
    a = (Rminus a' 1) ->
  (fun pm : (state * state) =>
     F2R (pm.1 (of_nat 1)).1 = exp eps * F2R (pm.2 (of_nat 1)).1
  /\
  F2R (pm.1 (of_nat 2)).1 = F2R (pm.2 (of_nat 2)).1
  /\  F2R (pm.1 (of_nat 2)).1 = 1 ) ->>
  (fun pm : (state * state) =>
   forall v : R,
   exp (((v - Lam) / 2 - a) * eps / F2R (pm.1 (of_nat 2)).1) <= F2R (pm.1 (of_nat 1)).1 <=
   exp (((v + Lam) / 2 - a) * eps / F2R (pm.1 (of_nat 2)).1) ->
   exp (((v - Lam) / 2 - a') * eps / F2R (pm.2 (of_nat 2)).1) <= F2R (pm.2 (of_nat 1)).1 <=
   exp (((v + Lam) / 2 - a') * eps / F2R (pm.2 (of_nat 2)).1)).

Proof.
move =>  a a' Lam B eps HLam HB Heps Hadj.
unfold assert_implies.   
simpl.
move => st1 st2 [H1 [H2 H3]] v Hp.

rewrite H1 in Hp.

rewrite H3 in H2.
rewrite H3 in Hp.

rewrite Hadj in Hp.
rewrite !( Rplus_minusopp ((v - Lam) / 2) (a' - 1)) in Hp.

rewrite Ropp_minus_distr in Hp.
rewrite !( Rplus_minusopp 1 a') in Hp.
rewrite (Rplus_comm 1 (-a')) in Hp.

rewrite <- (Rplus_assoc ((v - Lam) / 2) (-a') 1) in Hp.
rewrite <- (Rplus_minusopp ((v - Lam) / 2) a') in Hp.
rewrite (Rmult_plus_distr_r ((v - Lam) / 2 - a') 1 eps) in Hp.
rewrite Rmult_1_l in Hp.
rewrite Rmult_div in Hp.
rewrite Rinv_1 in Hp.

rewrite Rmult_1_r in Hp.
rewrite (Rexp_plus (((v - Lam) / 2 - a') * eps) eps) in Hp.
rewrite Rmult_comm in Hp.
inversion Hp as [Hp1 Hp2].
have Rexp_0 : 0 < exp eps.
apply Rexp_ge0.
apply (Rmult_le_reg_l (exp eps) (exp (((v - Lam) / 2 - a') * eps)) (F2R (st2 (of_nat 1)).1 ) Rexp_0) in Hp1.
rewrite <-!H2.
rewrite !Rmult_div.
rewrite !Rinv_1.

rewrite !Rmult_1_r.
split.
assumption.
rewrite !( Rplus_minusopp ((v + Lam) / 2) (a' - 1)) in Hp2.

rewrite Ropp_minus_distr in Hp2.
rewrite Rplus_minusopp in Hp2.
rewrite (Rplus_comm 1 (-a')) in Hp2.
rewrite <- Rplus_assoc in  Hp2.
rewrite <- Rplus_minusopp in Hp2.
rewrite (Rmult_plus_distr_r ((v + Lam) / 2 - a') 1 eps) in Hp2.
rewrite Rmult_1_l in Hp2.
rewrite Rmult_div in Hp2.
rewrite Rinv_1 in Hp2.

rewrite Rmult_1_r in Hp2.
rewrite (Rexp_plus (((v + Lam) / 2 - a') * eps) eps) in Hp2.
rewrite Rmult_comm in Hp2.
by apply (Rmult_le_reg_r (exp eps) (F2R (st2 (of_nat 1)).1 ) (exp (((v + Lam) / 2 - a') * eps)) Rexp_0) in Hp2.
Qed.


Lemma Snap_sub2:
  forall a a' Lam B eps: R,
     Rlt 0 Lam -> Rlt 0 B -> Rlt 0 eps->
     a = (Rminus a' 1)  ->
      (fun pm : (state * state) =>
     forall v : R,
   exp (((v - Lam) / 2 - a) * eps / F2R (pm.1 (of_nat 2)).1) <= F2R (pm.1 (of_nat 1)).1 <=
   exp (((v + Lam) / 2 - a) * eps / F2R (pm.1 (of_nat 2)).1) ->
   exp (((v - Lam) / 2 - a') * eps / F2R (pm.2 (of_nat 2)).1) <= F2R (pm.2 (of_nat 1)).1 <=
   exp (((v + Lam) / 2 - a') * eps / F2R (pm.2 (of_nat 2)).1)) ->>
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
               forall v, F2R (pm.1 (of_nat 3)).1 = v -> F2R (pm.2 (of_nat 3)).1 = v)
  .
Proof.
  move =>    a a' Lam B eps  HLam HB Heps Hadj.
  unfold assn_sub'.
  move => st1 st2 H v.
  simpl in H.
  rewrite /fst.
  rewrite /snd.
    (* rewrite <- forall_extensionalityP. *)
  move => Hst1.
  apply Rlt_le  in HB.
  apply Rle_rle in HB.
  

Admitted.

Ltac apply_snap_sub1 := apply Snap_sub1.



Lemma SnapDP:
  forall a a' Lam B eps: R,
     Rlt 0 Lam -> Rlt 0 B -> Rlt 0 eps->
     a = (Rminus a' 1) ->
    aprHoare_judgement ATrue (Snap a Lam B eps) (Rmult eps (Rplus 1 (Rmult 24%R (Rmult B eta)))) (Snap a' Lam B eps)
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
  eapply aprHoare_unif.
  move => * //.
  instantiate (2 :=  fun pm : (state * state) => F2R (pm.1 (of_nat 2)).1 = 1).
  
  instantiate (2 := eps).
  instantiate
    (1 := (fun pm : (state * state) =>
                forall v : R,
   exp (((v - Lam) / 2 - a) * eps / F2R (pm.1 (of_nat 2)).1) <= F2R (pm.1 (of_nat 1)).1 <=
   exp (((v + Lam) / 2 - a) * eps / F2R (pm.1 (of_nat 2)).1) ->
   exp (((v - Lam) / 2 - a') * eps / F2R (pm.2 (of_nat 2)).1) <= F2R (pm.2 (of_nat 1)).1 <=
   exp (((v + Lam) / 2 - a') * eps / F2R (pm.2 (of_nat 2)).1))).

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
  eapply aprHoare_conseq.
  eapply aprHoare_asgn.
  eapply Snap_sub2.

  assumption.
  assumption.
  assumption.
  assumption.
  unfold assert_implies.
  move => st1 st2 hp //.
  rewrite <- Rle_rle.
  lra.
  
Qed.

(*** weakest precondition formulation 
for example: replace the results to be equality **)
  Close Scope aprHoare_scope.
Close Scope R_scope.
