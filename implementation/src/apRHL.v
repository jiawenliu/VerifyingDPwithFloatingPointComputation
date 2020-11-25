

From Coq
     Require Import QArith.QArith QArith.Qminmax QArith.Qabs QArith.Qreals
     micromega.Psatz Reals.Reals.

From Snapv
     Require Import Command CommandSemantics ExpressionTransitions Environments.

From Snapv 
    Require Import  Maps.
From Snapv.distr Require Import Extra Prob.


Require Import Coq.Strings.Ascii Coq.Strings.BinaryString.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice seq.

From extructures Require Import ord fset fmap ffun.


(* ################################################################# *)
(** * Definitions *)
Definition Assertion :=( state * state) -> Prop.

Definition ATrue :=
  fun (pm : (state * state)) => True.

Definition AFalse :=
  fun (pm : (state * state)) => False.


Print state.

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

(***************************** The Formal Probabilistic Lifting Judgement ***************)


Definition prob_lifting (d1: distr_m) (P: Assertion) (eps: R) (d2: distr_m) : Prop := True.

(********************************* The Formal aprHoare Judgement *************************)


Definition aprHore_judgement (P: Assertion) (c1 : command) (eps: R) (c2: command) (Q: Assertion) : Prop
      :=
        forall st1 st2 distr1 distr2, (P (st1, st2)) ->
                                      (trans_com eta st1 c1 distr1) ->
                                      (trans_com eta st2 c2 distr2) ->
                                      prob_lifting distr1 Q eps distr2.


Notation "{{ P }} c1 { eps } c2 {{ Q }}" :=
  ( aprHore_judgement  P c1 eps c2 Q) (at level 90, c1 at level 91)
  : aprHoare_scope.

Print Grammar constr.

(* Check ({{ ATrue }} SKIP { 0.1%R } SKIP {{ ATrue }} ).
*)

(************************* The proving rules for aprHoare Logic Judgements ***************)


Theorem aprHore_skip : forall c1 c2 P ,
    aprHore_judgement  P c1 0 c2 P.
Proof.
  unfold aprHore_judgement.

  intros.
  unfold prob_lifting.
  auto.
Qed.


Theorem aprHore_asgn : forall x1 x2 e1 e2  Q,
    aprHore_judgement (assn_sub x1 x2 e1 e2 Q) (ASGN (Var x1) e1) 0 (ASGN (Var x2) e2) Q.
Proof.
  unfold aprHore_judgement.
  intros.
  unfold prob_lifting.
  auto.
Qed.



Theorem aprHore_seq : forall P c1 d1 R c2 d2 Q r1 r2 ,
    aprHore_judgement P c1 r1 c2 R -> aprHore_judgement R d1 r2 d2 Q 
    -> aprHore_judgement P (SEQ c1 d1) (r1 + r2) (SEQ c2 d2) R.
Proof.
  unfold aprHore_judgement.
  intros.
  unfold prob_lifting.
  auto.
Qed.



Theorem aprHore_conseq : forall (P Q P' Q' : Assertion) c1 c2 r r',
    aprHore_judgement P' c1 r' c2 Q' ->
    P ->> P' ->
    Q' ->> Q ->
    Rle r' r ->
    aprHore_judgement P c1 r c2 Q.
Proof.
  unfold aprHore_judgement.
  intros.
  unfold prob_lifting.
  auto.
Qed.


Theorem aprHore_unifP :forall x1 x2 eps,
   aprHore_judgement  ATrue (UNIF1 (Var x1)) eps (UNIF1 (Var x2))
                 (fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat x1)),(m2 (of_nat x2)) with
                                  | (v1, _),(v2, _) =>
                                    forall l r,
                                      Rlt l v1 -> Rlt v1 r -> Rlt (Rmult eps l) v2 -> Rlt v2 (Rmult eps r)
                                  end
                    end).
Proof.
  unfold aprHore_judgement.
  intros.
  unfold prob_lifting.
  auto.
Qed.


Theorem aprHore_unifN :forall x1 x2 eps,
   aprHore_judgement  ATrue (UNIF1 (Var x1)) eps (UNIF1 (Var x2))
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



Theorem aprHore_null :forall x1 x2 eps,
   aprHore_judgement  ATrue (UNIF1 (Var x1)) eps (UNIF1 (Var x2))
                 (fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat x1)),(m2 (of_nat x2)) with
                                  | (v1, _),(v2, _) => v1 = v2
                                    
                                  end
                    end).
Proof.
  unfold aprHore_judgement.
  intros.
  unfold prob_lifting.
  auto.
Qed.

Close Scope aprHoare_scope.

