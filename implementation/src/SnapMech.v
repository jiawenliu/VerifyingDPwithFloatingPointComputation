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
              


Lemma Snap_subsub1: 
      forall (a B eps x : R) (st1: env),
        Rlt 0 B -> Rlt 0 eps ->  Num (st1 (of_nat 2)).1 = 1 ->
        exp ((x - a) * eps / Num (st1 (of_nat 2)).1) <= Num (st1 (of_nat 1)).1
        ->
       x <= a + 1 / eps * (Num (st1 (of_nat 2)).1 * ln (Num (st1 (of_nat 1)).1)) 
.
Proof.
 move =>    a B eps x st1  HB Heps Hs H.
 apply (Rplus_le_reg_r (-a)).
  rewrite (Rplus_comm a).
  rewrite (Rplus_assoc _ a).
  
  rewrite Rplus_opp_r.
  rewrite Rplus_0_r.
  apply Rmult_div_inv_le.

  apply Rdiv_gt0.
  rewrite Rinv_inv_simpl.
  rewrite Rinv_involutive.
  assumption.
  have eps_neq0 : eps <> 0.
  
  apply Rgt_not_eq.
  assumption.
  apply Rgt_not_eq.
  assumption.
    apply Rmult_div_inv_le.

  rewrite Hs.
  lra.
  rewrite Rdiv_inv_mult_assoc.
  rewrite Rinv_involutive.
  apply Rexp_ln_le.
  rewrite -Rplus_minusopp.
  assumption.
  apply Rgt_not_eq.
  assumption.
Qed.

Lemma Snap_subsub2: 
      forall (a B eps x : R) (st1: env),
        Rlt 0 B -> Rlt 0 eps ->  Num (st1 (of_nat 2)).1 = 1 ->
        Num (st1 (of_nat 1)).1 <= exp ((x - a) * eps / Num (st1 (of_nat 2)).1)
        ->
       a + 1 / eps * (Num (st1 (of_nat 2)).1 * ln (Num (st1 (of_nat 1)).1))  <= x
.
Proof.
   move =>    a B eps x st1  HB Heps Hs H.
apply (Rplus_le_reg_r (-a)).
  rewrite (Rplus_comm a).
  rewrite (Rplus_assoc _ a).
  
  rewrite Rplus_opp_r.
  rewrite Rplus_0_r.
  apply Rmult_div_inv_le_l.

  apply Rdiv_gt0.
  rewrite Rinv_inv_simpl.
  rewrite Rinv_involutive.
  assumption.
  have eps_neq0 : eps <> 0.
  
  apply Rgt_not_eq.
  assumption.
  apply Rgt_not_eq.
  assumption.
    apply Rmult_div_inv_le_l.

  rewrite Hs.
  lra.
  rewrite Rdiv_inv_mult_assoc.
  rewrite Rinv_involutive.
  apply Rln_exp_le.
  rewrite -Rplus_minusopp.
  assumption.
  apply Rgt_not_eq.
  assumption.
Qed.
   
Lemma Snap_subsub3: 
      forall (a Lam B eps v : R) (st1: env),
        Rlt 0 Lam -> Rlt 0 B -> Rlt 0 eps  ->  Num (st1 (of_nat 2)).1 = 1 ->
         exp ((v - Lam / 2 - a) * eps / Num (st1 (of_nat 2)).1) <= Num (st1 (of_nat 1)).1 <=
         exp ((v + Lam / 2 - a) * eps / Num (st1 (of_nat 2)).1) ->
     v - Lam / 2 <= a + 1 / eps * (Num (st1 (of_nat 2)).1 * ln (Num (st1 (of_nat 1)).1)) <=
     v + Lam / 2
.
Proof.
  
   move =>    a  Lam B eps v st1 HLam HB Heps Hs H.

   split.
   eapply Snap_subsub1 with (B := B).
   assumption.
   assumption.
   assumption.
   apply H.
    eapply Snap_subsub2 with (B := B).
   assumption.
   assumption.
   assumption.
      apply H.

Qed.


Lemma Snap_subsub4: 
      forall (a Lam B eps v : R) (st1: env),
        Rlt 0 Lam -> Rlt 0 B -> Rlt 0 eps  ->  Num (st1 (of_nat 2)).1 = 1 ->
     v - Lam / 2 <= a + 1 / eps * (Num (st1 (of_nat 2)).1 * ln (Num (st1 (of_nat 1)).1)) <=
     v + Lam / 2
     ->
     exp ((v - Lam / 2 - a) * eps / Num (st1 (of_nat 2)).1) <= Num (st1 (of_nat 1)).1 <=
         exp ((v + Lam / 2 - a) * eps / Num (st1 (of_nat 2)).1)
.
Proof.
  move =>    a  Lam B eps v st1 HLam HB Heps Hs [H1 H2].
  split.
  apply Rexp_ln_le.
  apply Rmult_div_inv_le.

  rewrite Hs.
  lra.
  apply Rmult_div_inv_le_r.
  assumption.
  apply (Rplus_le_reg_r a).
  rewrite Rplus_minusopp.
  rewrite (Rplus_assoc _ _ a).

     rewrite Rplus_opp_l.
  rewrite Rplus_0_r.

  rewrite (Rplus_comm _ a).
  assumption.

  apply Rln_exp_le.
  apply Rmult_div_inv_le_l.
rewrite Hs.
lra.
 rewrite  Rdiv_mult_inv_le.
  apply (Rplus_le_reg_l a).
  rewrite -(Rplus_assoc a).
  rewrite (Rplus_comm _ (-a)).
  rewrite -(Rplus_assoc (-a)).
     rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  assumption.
  assumption.
  
Qed.


  
Lemma Snap_sub2:
  forall a a' Lam B eps: R,
     Rlt 0 Lam -> Rlt 0 B -> Rlt 0 eps->
     a = (Rminus a' 1)  ->
      (fun pm : (state * state) =>
    ( forall v : R,
   exp ((v - Lam / 2 - a) * eps / F2R (pm.1 (of_nat 2)).1) <= F2R (pm.1 (of_nat 1)).1 <=
   exp ((v + Lam / 2 - a) * eps / F2R (pm.1 (of_nat 2)).1) ->
   exp ((v - Lam / 2 - a') * eps / F2R (pm.2 (of_nat 2)).1) <= F2R (pm.2 (of_nat 1)).1 <=
   exp ((v + Lam / 2 - a') * eps / F2R (pm.2 (of_nat 2)).1))  /\  F2R (pm.1 (of_nat 2)).1 = 1
        /\ 
  F2R (pm.1 (of_nat 2)).1 = F2R (pm.2 (of_nat 2)).1) ->>
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
  simpl.
  rewrite !updE.
  rewrite !eqxx. 
  simpl in H.
  unfold F2R in H.     
  inversion H as [H1 H2].
  inversion H2 as [H21 H22].
  rewrite /fst.
  rewrite /snd.
  (* rewrite <- forall_extensionalityP. *)
  simpl.
  unfold fln.
  unfold fmult.
  unfold fplus.
  unfold R2F.
  simpl.
  move => Hst1.
  apply clamp_eqV.
  rewrite <- clamp_eqV in Hst1.
  apply round_eqV.
  rewrite <- round_eqV in Hst1.
  eapply Snap_subsub3.
  assumption.
  apply HB.  
  assumption.
  rewrite -H22.
  assumption.

  apply (H1 v).
  eapply  Snap_subsub4.
  assumption.
 apply HB.  
  assumption.

  assumption.
  assumption.

Qed.



 (** TODO: adaopt this Lemma into the main Proof *)
Lemma Snap_sub1:
  forall a a' Lam B eps: R,
     Rlt 0 Lam -> Rlt 0 B -> Rlt 0 eps->
    a = (Rminus a' 1) ->
  (fun pm : (state * state) =>
     F2R (pm.1 (of_nat 1)).1 = exp eps * F2R (pm.2 (of_nat 1)).1
  /\
  F2R (pm.1 (of_nat 2)).1 = F2R (pm.2 (of_nat 2)).1
 /\  F2R (pm.1 (of_nat 2)).1 = 1) ->>
  (fun pm : (state * state) =>
  ( forall v : R,
   exp ((v - Lam / 2 - a) * eps / F2R (pm.1 (of_nat 2)).1) <= F2R (pm.1 (of_nat 1)).1 <=
   exp ((v + Lam / 2 - a) * eps / F2R (pm.1 (of_nat 2)).1) ->
   exp ((v - Lam / 2 - a') * eps / F2R (pm.2 (of_nat 2)).1) <= F2R (pm.2 (of_nat 1)).1 <=
   exp ((v + Lam / 2 - a') * eps / F2R (pm.2 (of_nat 2)).1))  /\  F2R (pm.1 (of_nat 2)).1 = 1
  /\ 
  F2R (pm.1 (of_nat 2)).1 = F2R (pm.2 (of_nat 2)).1).

Proof.
  move =>  a a' Lam B eps HLam HB Heps Hadj.
move => st1 st2 [H1 [H2 H3]].
simpl.
simpl in H1.

simpl in H2.
simpl in H3.
split.  
unfold assert_implies.   
move => v Hp.

rewrite H1 in Hp.

rewrite H3 in H2.
rewrite H3 in Hp.

rewrite Hadj in Hp.
rewrite !( Rplus_minusopp (v - Lam/ 2) (a' - 1)) in Hp.

rewrite Ropp_minus_distr in Hp.
rewrite !( Rplus_minusopp 1 a') in Hp.
rewrite (Rplus_comm 1 (-a')) in Hp.

rewrite <- (Rplus_assoc (v - Lam / 2) (-a') 1) in Hp.
rewrite <- (Rplus_minusopp (v - Lam / 2) a') in Hp.
rewrite (Rmult_plus_distr_r (v - Lam / 2 - a') 1 eps) in Hp.
rewrite Rmult_1_l in Hp.
rewrite Rmult_div in Hp.
rewrite Rinv_1 in Hp.

rewrite Rmult_1_r in Hp.
rewrite (Rexp_plus ((v - Lam / 2 - a') * eps) eps) in Hp.
rewrite Rmult_comm in Hp.
inversion Hp as [Hp1 Hp2].
have Rexp_0 : 0 < exp eps.
apply Rexp_ge0.
apply (Rmult_le_reg_l (exp eps) (exp ((v - Lam / 2 - a') * eps)) (F2R (st2 (of_nat 1)).1 ) Rexp_0) in Hp1.
rewrite <-!H2.
rewrite !Rmult_div.
rewrite !Rinv_1.

rewrite !Rmult_1_r.
split.
assumption.
rewrite !( Rplus_minusopp (v + Lam / 2) (a' - 1)) in Hp2.

rewrite Ropp_minus_distr in Hp2.
rewrite Rplus_minusopp in Hp2.
rewrite (Rplus_comm 1 (-a')) in Hp2.
rewrite <- Rplus_assoc in  Hp2.
rewrite <- Rplus_minusopp in Hp2.
rewrite (Rmult_plus_distr_r (v + Lam / 2 - a') 1 eps) in Hp2.
rewrite Rmult_1_l in Hp2.
rewrite Rmult_div in Hp2.
rewrite Rinv_1 in Hp2.

rewrite Rmult_1_r in Hp2.
rewrite (Rexp_plus ((v + Lam / 2 - a') * eps) eps) in Hp2.
rewrite Rmult_comm in Hp2.
  by apply (Rmult_le_reg_r (exp eps) (F2R (st2 (of_nat 1)).1 ) (exp ((v + Lam / 2 - a') * eps)) Rexp_0) in Hp2.
by split.  
Qed.




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
  eapply Snap_sub1.
  apply HLam.
  apply HB.
  apply Heps.
  apply Hadj.
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
