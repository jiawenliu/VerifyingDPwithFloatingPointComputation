
From Coq
     Require Import (* QArith.QArith QArith.Qminmax QArith.Qabs QArith.Qreals
     micromega.Psatz *) Reals.Reals.

From Snapv
     Require Import Command CommandSemantics ExpressionTransitions Environments.

From Snapv.distr Require Import Extra Prob.

From Snapv.lib Require Import MachineType.

Require Import Coq.Strings.Ascii Coq.Strings.BinaryString.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq
     ssrint rat ssrnum bigop path.

(*
From mathcomp Require Import ssralg.
Import GRing.

Delimit Scope R_scope with R.
 *)


From extructures Require Import ord fset fmap ffun.

From deriving Require Import deriving.
Require Import Coq.Strings.String.
Require Import Coq.Unicode.Utf8.

                           
(* ################################################################# *)
(** * Definitions *)

Definition spair : Type :=  (state * state).

Definition Assertion := spair -> Prop.


Definition ATrue :=
  fun (pm : (state * state)) => True.

Definition AFalse :=
  fun (pm : (state * state)) => False.


Definition eta : R := 0.00001%R.


Definition assn_sub X1 X2 e1 e2 (P: Assertion) : Assertion :=
  fun (pm : (state * state)) =>
    match pm with
      | (m1, m2) =>
    forall v1 v2 er11 er12 er21 er22,
      trans_expr eta m1 e1 (v1, (er11, er12)) ->
      trans_expr eta m2 e2 (v2, (er21, er22)) ->
      P (((upd m1 (of_nat X1) (v1, (er11, er12)))),  ((upd m2 (of_nat X2) (v2, (er21, er22)))))
    end.

Definition assn_sub' x1 x2 e1 e2 (P: Assertion) : Assertion :=
  fun (pm : (state * state)) =>
    match pm with
      | (m1, m2) =>
      P (((upd m1 (of_nat x1) ( expr_eval m1 e1))),  ((upd m2 (of_nat x2) ( expr_eval m2 e2))))
    end.


Notation "P [ X1 X2 |-> e1 e2 ]" := (assn_sub X1 X2 e1 e2 P) (at level 10).


(*Command * epsilon * command : P => Q*)
Inductive hoare_rule : Assertion -> command -> R -> command -> Assertion -> Prop :=
  | H_Skip  P:
      hoare_rule P (SKIP) 0 (SKIP) P
  | H_Asgn Q x1 a1 x2 a2 :
      hoare_rule (assn_sub x1 x2 a1 a2 Q) (ASGN (Var x1) a1) 0 (ASGN (Var x2) a2) Q
  | H_Seq  P c1 c2 Q d1 d2 R r1 r2:
      hoare_rule P c1 r1 d1 Q -> hoare_rule Q c2 r2 d2 R 
    -> hoare_rule P (SEQ c1 c2) (r1 + r2) (SEQ d1 d2) R
  | H_Consequence  : forall (P Q P' Q' : Assertion) c1 c2 r r',
    hoare_rule P' c1 r' c2 Q' ->
    (forall st1 st2, P (st1, st2) -> P' (st1, st2)) ->
    (forall st1 st2, Q' (st1, st2) -> Q (st1, st2)) ->
    Rle r' r ->
    hoare_rule P c1 r c2 Q
  | H_UnifP x1 x2 eps:
      hoare_rule ATrue (UNIF1 (Var x1)) eps (UNIF1 (Var x2))
                 (fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat x1)),(m2 (of_nat x2)) with
                                  | (v1, (er11, er12)),(v2, (er21, er22)) =>
                                    forall l r,
                                      Rlt l v1 -> Rlt v1 r -> Rlt (Rmult eps l) v2 -> Rlt v2 (Rmult eps l)
                                  end
                 end)
  | H_UnifN x1 x2 eps:
      hoare_rule ATrue (UNIF1 (Var x1)) eps (UNIF1 (Var x2))
                 (fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat x1)),(m2 (of_nat x2)) with
                                  | (v1, (er11, er12)),(v2, (er21, er22)) =>
                                    forall l r,
                                      Rlt l v1 -> Rlt v1 r -> Rlt (Rmult (Ropp eps) l) v2 -> Rlt v2 (Rmult (Ropp eps) l)
                                  end
                 end)
  | H_Null  x1 x2:
hoare_rule ATrue (UNIF2 (Var x1)) 0 (UNIF2 (Var x2))
(fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat x1)),(m2 (of_nat x2)) with
                                  | (v1, (er11, er12)),(v2, (er21, er22)) =>
                                      v1 = v2
                                  end
                 end)
.

Declare Scope aprHoare_scope.

Definition assert_implies {T : ordType} (P Q : (T * T) -> Prop) : Prop :=
  forall st1 st2, P (st1, st2) -> Q (st1, st2).

Notation "P ->> Q" := (assert_implies P Q)
                        (at level 80) : aprHoare_scope.

Open  Scope aprHoare_scope.

(***************************** The Formal Probabilistic Lifting Judgement *************************)

Open Scope prob_scope.

Local Open Scope ring_scope.


Definition DP_divergenceR (T : ordType) (eps : R) (dT1 dT2: {prob T}) (delta : R) :=
  forall x,
    fle ( (fsub ( Q2F (dT1 x)) ( fmult (f64exp (R2F64 eps)) (Q2F (dT2 x))))) (F64 delta) /\
    fle ( (fsub ( Q2F (dT2 x)) ( fmult (f64exp (R2F64 eps)) (Q2F (dT1 x))))) (F64 delta).


Lemma DP_divergenceR_implies T eps1 eps2 d1 d2:
  DP_divergenceR T eps1 d1 d2 0-> rle eps1 eps2 ->
  DP_divergenceR T eps2 d1 d2 0.
Proof.
  move => HI HE.
  unfold DP_divergenceR.
  unfold DP_divergenceR in HI.
  split.
  
  eapply fle_sub .
  apply fle_mult_left.
  apply fle_exp.
  apply rle_fle.
  apply HE.
  destruct (HI x) as [HI1 HI2].    
  assumption.
  eapply fle_sub .
  apply fle_mult_left.
  apply fle_exp.
  apply rle_fle.
  apply HE.
  destruct (HI x) as [HI1 HI2].    
  assumption.
Qed.


  
                                       



(*
The Formal Definition for Probabilistic Lifting
1. two jiont distributions of d1 and d2
2. marginal of each joint distirbution is d1 and d2
3. (eps, delta) distance < detla
 *)

Variant prob_lifting {T : ordType}  d1  (P : (T * T) -> Prop) (eps: R) d2 : Type :=
| Coupling dl dr of
  d1 = sample dl (dirac \o fst) &
  d2 = sample dr (dirac \o snd) &
  (forall xy, xy \in supp dl -> P (xy.1, xy.2)) &
  (forall xy, xy \in supp dr -> P (xy.1, xy.2)) &
  (DP_divergenceR ([ordType of (T * T) ]) eps dl dr (0)).




(******************************* The Formal aprHoare Judgement with Empty Prob Lifting Definition ********************************)


Lemma lifting_imply (T : ordType) (P P' : (T * T) -> Prop ) (eps1 eps2: R) d1 d2 :
  prob_lifting d1 P' eps1 d2 ->
  P' ->> P ->
  rle eps1 eps2 -> prob_lifting d1 P eps2 d2.
Proof.
  move => Hc Hp Heps.
  inversion Hc.
   exists dl dr.
   assumption.
   assumption.
   have Hp' : forall xy, P'(xy.1, xy.2) -> P(xy.1, xy.2).
   move=> [x y] Hyp.
   apply Hp.
   apply Hyp.
   eauto.
   eauto.
   eapply DP_divergenceR_implies.
   apply H3.
   apply Heps.
Qed.

Lemma lifting_dirac (T : ordType) (R : (T * T) -> Prop) x y :
  R (x, y) -> prob_lifting (dirac x) R 0 (dirac y).
Proof.  
  move => rxy; exists (dirac (x, y))  (dirac (x, y)); rewrite ?sample_diracL //.
    by move=> [??] /supp_diracP [-> ->].
    by move=> [??] /supp_diracP [-> ->].
    unfold DP_divergenceR.
    intros.
    split.
    eapply  fle_mult.
    apply qle_fle.      
    apply  distr_ge0.
    rewrite f0_eq .
    apply f0_le_exp.
    eapply fle_mult.
    apply qle_fle.
    apply distr_ge0.      
    rewrite f0_eq .
    apply f0_le_exp.      
Qed.

Lemma lifting_eq  (T : ordType) (d: {prob T}) :
  prob_lifting d (fun xy => xy.1 = xy.2)  0 d.
Proof.
  intros.
  pose dl := sample d (fun x => dirac (x, x)).
  pose dr := sample d (fun x => dirac (x, x)).
  exists dl dr.
  unfold dl.
  rewrite sampleA.
  under eq_sample do rewrite sample_diracL //.
                     simpl.
                     rewrite sample_diracR //.
  rewrite sampleA. 
  under eq_sample do rewrite sample_diracL //.
                     simpl.
                     rewrite sample_diracR //.
                     simpl.
  move=> [x y].
  simpl.
  rewrite supp_sample.
  case/bigcupP.
  move => i Hi Ht Hxy .
  rewrite supp_dirac in Hxy.
  rewrite in_fset1 in Hxy.
  have Hxy': (x, y) = (i, i).
  by apply /eqP.
    by inversion Hxy'.
  move=> [x y].
  simpl.
  rewrite supp_sample.
  case/bigcupP.
  move => i Hi Ht Hxy .
  rewrite supp_dirac in Hxy.
  rewrite in_fset1 in Hxy.
  have Hxy': (x, y) = (i, i).
  by apply /eqP.
    by inversion Hxy'.
    
  unfold dl.
  unfold dr. 
  unfold DP_divergenceR.
  intros.
  split.
  eapply  fle_mult.
  apply qle_fle.      
  apply  distr_ge0.
  rewrite f0_eq .
  apply f0_le_exp.
  eapply fle_mult.
  apply qle_fle.
  apply distr_ge0.      
  rewrite f0_eq .
  apply f0_le_exp.
Qed.



Unset Printing Implicit Defensive.


Arguments DP_divergenceR { _ } .

Lemma divergenceC:
    forall (T S : ordType) (eL eR: {prob T*T}) eps1 eps2 (drawR drawL: (T* T) -> {prob  S * S}),
      DP_divergenceR  eps1 eL eR 0 ->
      (forall x y, 
        (x, y) \in (supp eL :|: supp eR)%fset -> 
                   DP_divergenceR eps2 (drawL (x, y) ) (drawR (x, y) ) 0) ->
      DP_divergenceR (Rplus eps1 eps2) (sample eL drawL) (sample eR drawR) 0.
Proof.
  move => *.

  unfold DP_divergenceR.

  move => x.
  rewrite !sampleE.
  
  
Admitted.

Lemma divergenceC':
    forall (T S : ordType) (eL eR: {prob T*T}) eps (drawR drawL: (T*T) -> {prob S * S}),
      DP_divergenceR  eps eL eR 0 ->
      (forall x y, 
        (x, y) \in (supp eL :|: supp eR)%fset -> 
                   DP_divergenceR eps (drawL (x, y) ) (drawR (x, y) ) 0) ->
      DP_divergenceR eps (sample eL drawL) (sample eR drawR) 0.
Proof.
  move => *.

  unfold DP_divergenceR.

  move => x.
  rewrite !sampleE.
  
  
Admitted.


Lemma lifting_sample (T S : ordType) R1 R2 (d1 d2: {prob T}) (eps : R) (f g: T -> {prob S}) :
  prob_lifting d1 R1 eps d2 ->
  (forall x y, R1 (x, y) ->  prob_lifting (f x) R2 eps (g y)) ->
  prob_lifting (sample d1 f) R2 (eps) (sample d2 g).
Proof.
  case=> /= eL eR Ld1 Rd2 R1eL R1eR eps1D R12.
  pose def xy := sample: x' <- f xy.1; sample: y' <- g xy.2; dirac (x', y').
  have W xy : xy \in (supp eL :|: supp eR)%fset ->
              prob_lifting (f xy.1) R2 eps (g xy.2).
    rewrite in_fsetU.
    by case: (boolP (xy \in supp eL)) => [xy_in _|_ xy_in]; eauto.

   pose drawL xy :=
     if insub xy is Some xy
     then
       let: Coupling eT eS _ _ _ _ _  := W (sval xy) (svalP xy) in
       eT
     else
       def xy.
    
   pose drawR xy :=
     if insub xy is Some xy
     then
       let: Coupling eT eS _ _ _ _ _  := W (sval xy) (svalP xy) in
       eS
     else
       def xy.

   exists (sample eL drawL) (sample eR drawR).

  - rewrite Ld1 !sampleA; apply/eq_in_sample; case=> [x y] /= xy_supp.
    rewrite sample_diracL insubT /= ?in_fsetU ?xy_supp //.
      by move=> ?; case: (W _ _).

  - rewrite Rd2 !sampleA; apply/eq_in_sample; case=> [x y] /= xy_supp.
    rewrite sample_diracL insubT /= ?in_fsetU ?xy_supp ?orbT //.
      by move=> ?; case: (W _ _).

  - case=> x' y' /supp_sampleP [] [x y] xy_supp.
    rewrite /drawL insubT /= ?in_fsetU ?xy_supp //.
    move=> ?; case: (W _ _) => /= eL' eR' Ld1' Rd2' R1eL' R1eR' eps1D'; exact:  R1eL'.

  - case=> x' y' /supp_sampleP [] [x y] xy_supp.
    rewrite /drawR insubT /= ?in_fsetU ?xy_supp ?orbT // .
    move=> ?; case: (W _ _) => /= eL' eR' Ld1' Rd2' R1eL' R1eR' eps1D'; exact:  R1eR'.

    have eps2D: forall x y, 
        (x, y) \in (supp eL :|: supp eR)%fset -> 
                   R1 (x, y) ->
                   DP_divergenceR
                     eps (drawL (x, y) ) (drawR (x, y) ) 0.
    unfold drawL.
    unfold drawR.
    move => x y insubxy R1xy.
    rewrite insubT /=.
      by case: (W _ _ ).  

      have eps2D': forall x y, 
          (x, y) \in (supp eL :|: supp eR)%fset -> 
                     DP_divergenceR
                       eps (drawL (x, y) ) (drawR (x, y) ) 0.
      unfold drawL.
      unfold drawR.
      move => x y insubxy.
      rewrite insubT /=.
        by case: (W _ _ ).
        by apply divergenceC'.
Qed.
  



Lemma lifting_sample' (T S : ordType) R1 R2 (d1 d2: {prob T}) (eps1 eps2 : R) (f g: T -> {prob S}) :
  prob_lifting d1 R1 eps1 d2 ->
  (forall x y, R1 (x, y) ->  prob_lifting (f x) R2 eps2 (g y)) ->
  prob_lifting (sample d1 f) R2 (eps1 + eps2) (sample d2 g).
Proof.
  
  case=> /= eL eR Ld1 Rd2 R1eL R1eR eps1D R12.
  pose def xy := sample: x' <- f xy.1; sample: y' <- g xy.2; dirac (x', y').
  have W xy : xy \in (supp eL :|: supp eR)%fset ->
              prob_lifting (f xy.1) R2 eps2 (g xy.2).
    rewrite in_fsetU.
    by case: (boolP (xy \in supp eL)) => [xy_in _|_ xy_in]; eauto.

   pose drawL xy :=
     if insub xy is Some xy
     then
       let: Coupling eT eS _ _ _ _ _  := W (sval xy) (svalP xy) in
       eT
     else
       def xy.
    
   pose drawR xy :=
     if insub xy is Some xy
     then
       let: Coupling eT eS _ _ _ _ _  := W (sval xy) (svalP xy) in
       eS
     else
       def xy.

   exists (sample eL drawL) (sample eR drawR).

  - rewrite Ld1 !sampleA; apply/eq_in_sample; case=> [x y] /= xy_supp.
    rewrite sample_diracL insubT /= ?in_fsetU ?xy_supp //.
      by move=> ?; case: (W _ _).

  - rewrite Rd2 !sampleA; apply/eq_in_sample; case=> [x y] /= xy_supp.
    rewrite sample_diracL insubT /= ?in_fsetU ?xy_supp ?orbT //.
      by move=> ?; case: (W _ _).

  - case=> x' y' /supp_sampleP [] [x y] xy_supp.
    rewrite /drawL insubT /= ?in_fsetU ?xy_supp //.
    move=> ?; case: (W _ _) => /= eL' eR' Ld1' Rd2' R1eL' R1eR' eps1D'; exact:  R1eL'.

  - case=> x' y' /supp_sampleP [] [x y] xy_supp.
    rewrite /drawR insubT /= ?in_fsetU ?xy_supp ?orbT // .
    move=> ?; case: (W _ _) => /= eL' eR' Ld1' Rd2' R1eL' R1eR' eps1D'; exact:  R1eR'.

    have eps2D: forall x y, 
        (x, y) \in (supp eL :|: supp eR)%fset -> 
                   R1 (x, y) ->
                   DP_divergenceR
                     eps2 (drawL (x, y) ) (drawR (x, y) ) 0.
    unfold drawL.
    unfold drawR.
    move => x y insubxy R1xy.
    rewrite insubT /=.
      by case: (W _ _ ).  

      have eps2D': forall x y, 
          (x, y) \in (supp eL :|: supp eR)%fset -> 
                     DP_divergenceR
                       eps2 (drawL (x, y) ) (drawR (x, y) ) 0.
      unfold drawL.
      unfold drawR.
      move => x y insubxy.
      rewrite insubT /=.
        by case: (W _ _ ).
          by apply divergenceC.
Qed.

(***************** The Formal aprHoare Judgement with Full Prob Lifting Definition ******************)


Definition aprHoare_judgement (P: Assertion) (c1 : command) (eps: R) (c2: command) (Q: Assertion) 
  :=
    forall st1 st2,
    let distr1 := com_eval st1 c1 in
    let distr2 := com_eval st2 c2 in
   (P (st1, st2)) -> prob_lifting distr1 Q eps distr2.


Notation "{{ P }} c1 { eps } c2 {{ Q }}" :=
  ( aprHoare_judgement  P c1 eps c2 Q) (at level 90, c1 at level 91)
  : aprHoare_scope.

(* Check ({{ ATrue }} SKIP { 0.1%R } SKIP {{ ATrue }} ). *)

(************************* The Proving Rules for aprHoare Logic Judgements *************************)


(*  The SKIP aprHore Logic Rule  *)

Theorem aprHoare_skip : forall P ,
    aprHoare_judgement  P SKIP 0 SKIP P.
Proof.  
  unfold aprHoare_judgement.
  intros.
  apply lifting_dirac.
  apply H.
Qed.                

Theorem aprHoare_asgn : forall x1 x2 e1 e2  Q,
    aprHoare_judgement (assn_sub' x1 x2 e1 e2 Q) (ASGN (Var x1) e1) 0 (ASGN (Var x2) e2) Q.
Proof.
  unfold aprHoare_judgement. 
  intros.
  unfold assn_sub' in H.
  unfold com_eval.
  intros.
  apply lifting_dirac.
  apply H.
Qed.



Theorem aprHoare_seq : forall P c1 d1 R c2 d2 Q r1 r2 ,
    aprHoare_judgement P c1 r1 c2 R -> aprHoare_judgement R d1 r2 d2 Q 
    -> aprHoare_judgement P (SEQ c1 d1) (r1 + r2) (SEQ c2 d2) Q.
Proof. 
  unfold aprHoare_judgement.

  move => P c1 d1 R2 c2 d2 Q r1 r2 H1 H2 st1 st2 Hp.
  eapply lifting_sample'.
  by apply H1.
    by apply  H2.
Qed.


Theorem aprHoare_conseq : forall (P Q P' Q' : Assertion) c1 c2 r r',
    aprHoare_judgement P' c1 r' c2 Q' ->
    P ->> P' ->
    Q' ->> Q ->
    rle r' r ->
    aprHoare_judgement P c1 r c2 Q.
Proof.
  unfold aprHoare_judgement.
  intros.
  eapply lifting_imply .
  apply X.
  apply H.
  apply H2.
  apply H0.
  apply H1.
Qed.




Theorem aprHoare_null1 :forall x1 x2,
   aprHoare_judgement  ATrue (UNIF1 (Var x1)) (0 + 0) (UNIF1 (Var x2))
                 (fun (pm : (state * state)) => (pm.1 (of_nat x1)).1 = (pm.2 (of_nat x2)).1).
Proof.
  unfold aprHoare_judgement.
  move => x1 x2   st1 st2 HT.  

  eapply lifting_sample'.
  apply lifting_eq.
  intros.
  apply lifting_dirac.
  simpl.
  simpl in H.
  rewrite H.
  rewrite  !updE //.
  rewrite !eqxx.
  simpl.  
  reflexivity.
Qed.

Theorem aprHoare_null2 :forall x1 x2,
   aprHoare_judgement  ATrue (UNIF2 (Var x1)) (0 + 0) (UNIF2 (Var x2))
                (fun (pm : (state * state)) => (pm.1 (of_nat x1)).1 = (pm.2 (of_nat x2)).1).
Proof.
  unfold aprHoare_judgement.
  move => x1 x2   st1 st2 HT.  
  eapply lifting_sample'.
  apply lifting_eq.
  intros.
  apply lifting_dirac.
  simpl.
  simpl in H.
  rewrite H.
  rewrite  !updE //.
  rewrite !eqxx.
  simpl.  
  reflexivity.
Qed.

Lemma lifting_unif  eps:
    prob_lifting Unif.unif_01
                 (fun xy => forall l r, Rlt l xy.1 -> Rlt xy.1 r -> Rlt (Rmult eps l) xy.2 -> Rlt xy.2 (Rmult eps r))
eps Unif.unif_01.

Proof.
Admitted.



Theorem aprHoare_unifP :forall x1 x2 eps,
   aprHoare_judgement  ATrue (UNIF1 (Var x1)) (eps+0) (UNIF1 (Var x2))
                 (fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat x1)),(m2 (of_nat x2)) with
                                  | (v1, _),(v2, _) =>
                                    forall l r,
                                      Rlt l v1 -> Rlt v1 r -> Rlt (Rmult eps l) v2 -> Rlt v2 (Rmult eps r)
                                  end
                    end).
Proof.
  unfold aprHoare_judgement.
  move => x1 x2 eps  st1 st2 HT.  
  eapply lifting_sample'.
  apply lifting_unif.
   intros.
  apply lifting_dirac.
  simpl.
  simpl in H.
  
  rewrite  !updE //.
  by rewrite !eqxx.
Qed.


Lemma lifting_unifN  eps:
    prob_lifting Unif.unif_01
                 (fun xy => forall l r, Rlt l xy.1 -> Rlt xy.1 r -> Rlt (Rmult  (Ropp eps) l) xy.2 -> Rlt xy.2 (Rmult  (Ropp eps) r))
eps Unif.unif_01.

Proof.
Admitted.




Theorem aprHoare_unifN :forall x1 x2 eps,
   aprHoare_judgement  ATrue (UNIF1 (Var x1)) (eps + 0) (UNIF1 (Var x2))
                 (fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat x1)),(m2 (of_nat x2)) with
                                  | (v1, _),(v2, _) =>
                                    forall l r,
                                      Rlt l v1 -> Rlt v1 r -> Rlt (Rmult (Ropp eps) l) v2 -> Rlt v2 (Rmult (Ropp eps) r)
                                  end
                    end).
Proof.

  unfold aprHoare_judgement.
  move => x1 x2 eps  st1 st2 HT.  
  eapply lifting_sample'.
  apply lifting_unifN.
   intros.
  apply lifting_dirac.
  simpl.
  simpl in H.
  
  rewrite  !updE //.
  by rewrite !eqxx.
Qed.





Theorem aprHoare_round :forall y1 y2 x1 x2 Lam,
   aprHore_judgement (fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat y1)),(m2 (of_nat y2)) with
                                  | (v1, _),(v2, _) => 
                                  forall v, 
                                  (Rle v1 (v + Lam/2)) /\ (Rle (v - Lam/2) v1) -> 
                                    (Rle v2 (v + Lam/2)) /\ (Rle (v - Lam/2) v2)                           
                                  end
                    end)
                     (ASGN (Var x1) (Binop Round (Const Lam) (Var y1))) 0
                     (ASGN (Var x2) (Binop Round (Const Lam) (Var y2)))
                 (fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat x1)),(m2 (of_nat x2)) with
                                  | (v1, _),(v2, _) => forall v, v1 = v -> v2 = v
                                    
                                  end
                    end).
Proof.
  unfold aprHore_judgement.
  intros.
  unfold prob_lifting.
  auto.
Qed.


(*************************************** Some Logic Lemmas and Theorems ********************************)


Theorem hoare_pre_false : forall (Q : Assertion) c1 c2,
  aprHore_judgement AFalse c1 0 c2 Q.
Proof.
  unfold aprHore_judgement.
  intros.
  unfold prob_lifting.
  auto.
Qed.


Theorem hoare_post_true : forall(P : Assertion) c1 c2,
  aprHore_judgement P c1 0 c2 ATrue.
Proof.
 unfold aprHore_judgement.
  intros.
  unfold prob_lifting.
  auto.
Qed.

Close Scope ring_scope.

Close Scope aprHoare_scope.
Close Scope prob_scope.
