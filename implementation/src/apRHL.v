
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

From extructures Require Import ord fset fmap ffun.

From deriving Require Import deriving.
Require Import Coq.Strings.String.
Require Import Coq.Unicode.Utf8.

(* ################################################################# *)
(** * Definitions *)
Definition Assertion :=( state * state) -> Prop.

Definition ATrue :=
  fun (pm : (state * state)) => True.

Definition AFalse :=
  fun (pm : (state * state)) => False.

Definition eta := 0.00001%R.

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

Definition assert_implies (P Q : Assertion) : Prop :=
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

(* \max *)


(*
Definition DP_divergence (T : ordType) (eps : R) (dT1 dT2: {prob T}) :=

 \max_(x <- supp dT1) 
 if (x \in supp dT2) then (subq (dT1 x) ( mulq eps (dT2 x)))
 else (dT1 x).



Definition DP_divergence_m (eps : R) (dT1 dT2: distr_m) := 
 \max_(x <- supp dT1) 
 if (x \in supp dT2) then (subq (dT1 x) ( mulq eps (dT2 x)))
 else (dT1 x).
*)



Definition prob_lifting (d1: distr_m) (P: Assertion) (eps: R) (d2: distr_m) : Prop :=
  True.

(*
The Formal Definition for Probabilistic Lifting
1. two jiont distributions of d1 and d2
2. marginal of each joint distirbution is d1 and d2
3. (eps, delta) distance < detla
 *)

Variant prob_lifting' (d1: distr_m) (P: Assertion) (eps: R) (d2: distr_m) : Type :=
| Coupling dl dr of
  d1 = sample dl (dirac \o fst) &
  d2 = sample dr (dirac \o snd) &
  (forall xy, xy \in supp dl -> P (xy.1, xy.2)) &
  (forall xy, xy \in supp dr -> P (xy.1, xy.2)) &
  (DP_divergenceR ([ordType of (state * state)]) eps dl dr (0)).

(********************************* The Formal aprHoare Judgement with Empty Prob Lifting Definition ***********************************)

Lemma lifting_dirac (R : Assertion) x y :
  R (x, y) -> prob_lifting' (dirac x) R 0 (dirac y).
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

Unset Printing Implicit Defensive.

Lemma lifting_sample (R1 R2 : Assertion) (d1 d2 : distr_m) (eps1 eps2 : R) f g :
  prob_lifting' d1 R1 eps1 d2 ->
  (forall x y, x \in supp d1 -> y \in supp d2 -> R1 (x, y) ->  prob_lifting' (f x) R2 eps2 (g y)) ->
  prob_lifting' (sample d1 f) R2 (eps1 + eps2) (sample d2 g).
Proof.
case=> /= eL eR Ld1 Rd2 R1eL R1eR eps1D R12.
pose def xy := sample: x' <- f xy.1; sample: y' <- g xy.2; dirac (x', y').
pose P xy := (xy \in supp eL) && (xy \in supp eR).
have WT xy : P xy -> xy.1 \in supp d1.
  move=> /andP [xyp _]; rewrite Ld1; apply/supp_sampleP.
  exists xy=> //=; exact/supp_diracP.
have WS xy : P xy -> xy.2 \in supp d2.
  move=> /andP [_ xyp]; rewrite Rd2; apply/supp_sampleP.
  exists xy=> //=; exact/supp_diracP.
have WR1 xy : P xy -> R1 xy.
  case: xy => x y.
  case/andP => ??.
  by apply: (R1eL (x, y)).
have {}R12 : forall xy, xy.1 \in supp d1 -> xy.2 \in supp d2 ->
               R1 xy -> prob_lifting' (f xy.1) R2 eps2 (g xy.2).
  by move=> [x y]; apply: R12.
pose drawL xy := if insub xy is Some xy
                 then
                   let xyP := svalP xy in
                   let xP := WT (sval xy) xyP in
                   let yP := WS (sval xy) xyP in
                   let: Coupling eT eS _ _ _ _ _  :=
                      R12 (sval xy) xP yP (WR1 _ xyP) in
                   eT
                 else
                   def xy.
pose drawR xy := if insub xy is Some xy
                 then
                   let xyP := svalP xy in
                   let xP := WT _ xyP in
                   let yP := WS _ xyP in
                   let: Coupling eT eS _ _ _ _ _  :=
                      R12 (sval xy) xP yP (WR1 _ xyP) in
                   eS
                 else
                   def xy.
exists (sample eL drawL) (sample eR drawR).

 (* exists (sample eL (drawL)) (sample eR drawR).*)
(* SIMPLify the proof*)
Admitted.


Lemma lifting_sample' (R1 R2 : Assertion) (d1 d2 : distr_m) (eps1 eps2 : R) f g :
  prob_lifting' d1 R1 eps1 d2 ->
  (forall x y, R1 (x, y) ->  prob_lifting' (f x) R2 eps2 (g y)) ->
  prob_lifting' (sample d1 f) R2 (eps1 + eps2) (sample d2 g).
Proof.
  
  case=> /= eL eR Ld1 Rd2 R1eL R1eR eps1D R12.
  pose def xy := sample: x' <- f xy.1; sample: y' <- g xy.2; dirac (x', y').
  
 have WT xy : xy \in supp eL -> xy.1 \in supp d1.
  move=> xyp; rewrite Ld1; apply/supp_sampleP.  
  exists xy=> //=; exact/supp_diracP.
have WS xy : xy \in supp eR -> xy.2 \in supp d2.
  move=> xyp; rewrite Rd2; apply/supp_sampleP.
  exists xy=> //=; exact/supp_diracP.
  (* pose drawR xy :=
     let xyP := svalP xy in
                    let xP := WS _ xyP in
                    let: Coupling  _ eT _ _ _ _ _
                       := R12   xP (R1eR  _ xyP)
                    in eT.*)
   exists (sample eL def) (sample eR def).

  
  Admitted.

Definition aprHoare_judgement (P: Assertion) (c1 : command) (eps: R) (c2: command) (Q: Assertion) : Prop
      :=
        forall st1 st2 distr1 distr2, (P (st1, st2)) ->
                                      (trans_com eta st1 c1 distr1) ->
                                      (trans_com eta st2 c2 distr2) ->
                                      prob_lifting distr1 Q eps distr2.

(********************************* The Formal aprHoare Judgement with Full Prob Lifting Definition ***********************************)


Definition aprHoare_judgement' (P: Assertion) (c1 : command) (eps: R) (c2: command) (Q: Assertion) 
  :=
    forall st1 st2,
    let distr1 := com_eval st1 c1 in
    let distr2 := com_eval st2 c2 in
   (P (st1, st2)) -> prob_lifting' distr1 Q eps distr2.


Notation "{{ P }} c1 { eps } c2 {{ Q }}" :=
  ( aprHoare_judgement  P c1 eps c2 Q) (at level 90, c1 at level 91)
  : aprHoare_scope.

(* Check ({{ ATrue }} SKIP { 0.1%R } SKIP {{ ATrue }} ).
*)

(************************* The Proving Rules for aprHoare Logic Judgements *************************)


(*  The SKIP aprHore Logic Rule  *)

Theorem aprHoare_skip : forall P ,
    aprHoare_judgement'  P SKIP 0 SKIP P.
Proof.  
  unfold aprHoare_judgement'.
  intros.
  apply lifting_dirac.
  apply H.
Qed.                

Theorem aprHoare_asgn : forall x1 x2 e1 e2  Q,
    aprHoare_judgement' (assn_sub' x1 x2 e1 e2 Q) (ASGN (Var x1) e1) 0 (ASGN (Var x2) e2) Q.
Proof.
  unfold aprHoare_judgement'. 
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
  intros.
  unfold prob_lifting.
  auto.
Qed.


Theorem aprHoare_seq' : forall P c1 d1 R c2 d2 Q r1 r2 ,
    aprHoare_judgement' P c1 r1 c2 R -> aprHoare_judgement' R d1 r2 d2 Q 
    -> aprHoare_judgement' P (SEQ c1 d1) (r1 + r2) (SEQ c2 d2) Q.
Proof.
  unfold aprHore_judgement'.

  intros.
  case=> /= p.
  pose def xy := sample: x' <- com_eval xy.1 c2; sample: y' <- com_eval xy.2 d2; dirac (x', y').
  have WT xy : xy \in supp (state * state) -> xy.1 \in supp (state).
  move=> xyp; rewrite eT; apply/supp_sampleP.
  unfold com_eval.
Qed.


Theorem aprHoare_conseq : forall (P Q P' Q' : Assertion) c1 c2 r r',
    aprHoare_judgement P' c1 r' c2 Q' ->
    P ->> P' ->
    Q' ->> Q ->
    Rle r' r ->
    aprHoare_judgement P c1 r c2 Q.
Proof.
  unfold aprHoare_judgement.
  intros.
  unfold prob_lifting.
  auto.
Qed.


Theorem aprHoare_unifP :forall x1 x2 eps,
   aprHoare_judgement  ATrue (UNIF1 (Var x1)) eps (UNIF1 (Var x2))
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
  intros.
  unfold prob_lifting.
  auto.
Qed.


Theorem aprHoare_unifN :forall x1 x2 eps,
   aprHoare_judgement  ATrue (UNIF1 (Var x1)) eps (UNIF1 (Var x2))
                 (fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat x1)),(m2 (of_nat x2)) with
                                  | (v1, _),(v2, _) =>
                                    forall l r,
                                      Rlt l v1 -> Rlt v1 r -> Rlt (Rmult (Ropp eps) l) v2 -> Rlt v2 (Rmult (Ropp eps) r)
                                  end
                    end).
Proof.
  unfold aprHore_judgement.
  intros.
  unfold prob_lifting.
  auto.
Qed.



Theorem aprHoare_null :forall x1 x2,
   aprHore_judgement  ATrue (UNIF1 (Var x1)) 0 (UNIF1 (Var x2))
                 (fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat x1)),(m2 (of_nat x2)) with
                                  | (v1, _),(v2, _) => v1 = v2
                                    
                                  end
                    end).
Proof.
  unfold aprHoare_judgement.
  intros.
  unfold prob_lifting.
  auto.
Qed.

Theorem aprHoare_nulls :forall x1 x2,
   aprHore_judgement  ATrue (UNIF2 (Var x1)) 0 (UNIF2 (Var x2))
                 (fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat x1)),(m2 (of_nat x2)) with
                                  | (v1, _),(v2, _) => v1 = v2
                                    
                                  end
                    end).
Proof.
  unfold aprHoare_judgement.
  intros.
  unfold prob_lifting.
  auto.
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
