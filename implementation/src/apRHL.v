

From Coq
     Require Import QArith.QArith QArith.Qminmax QArith.Qabs QArith.Qreals
     micromega.Psatz Reals.Reals.

From Snapv
     Require Import Infra.RationalSimps Infra.RealRationalProps
     Infra.RealSimps Infra.Ltacs.

From Snapv
     Require Import Command CommandSemantics ExpressionTransitions.

From Snapv 
    Require Import Hoare  Maps.
From Snapv.aprhl Require Import Extra Prob.


Require Import Coq.Strings.Ascii Coq.Strings.BinaryString.


(* ################################################################# *)
(** * Definitions *)
Definition Assertion :=( state * state) -> Prop.

Definition ATrue :=
  fun (pm : (state * state)) => True.

Definition AFalse :=
  fun (pm : (state * state)) => False.


Print state.

Definition delta := 0.00001%R.

Definition assn_sub X1 X2 e1 e2 (P: Assertion) : Assertion :=
  fun (pm : (state * state)) =>
    match pm with
      | (m1, m2) =>
    forall v1 v2 er11 er12 er21 er22,
      trans_expr m1 delta e1 (v1, (er11, er12)) ->
      trans_expr m2 delta e2 (v2, (er21, er22)) ->
      P (((t_update m1 (of_nat X1) (v1, (er11, er12)))),  ((t_update m2 (of_nat X2) (v2, (er21, er22)))))
      end.

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).



Inductive hoare_rule : Assertion -> command R -> R -> command R -> Assertion -> Prop :=
  | H_Skip  P:
      hoare_rule P (SKIP R) 0 (SKIP R) P
  | H_Asgn Q x1 a1 x2 a2 :
      hoare_rule (assn_sub x1 x2 a1 a2 Q) (ASGN (Var R x1) a1) 0 (ASGN (Var R x2) a2) Q
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
      hoare_rule ATrue (UNIF1 (Var R x1)) eps (UNIF1 (Var R x2))
                 (fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat x1)),(m2 (of_nat x2)) with
                                  | (v1, (er11, er12)),(v2, (er21, er22)) =>
                                    forall l r,
                                      Rlt l v1 -> Rlt v1 r -> Rlt (Rmult eps l) v2 -> Rlt v2 (Rmult eps l)
                                  end
                 end)
  | H_UnifN x1 x2 eps:
      hoare_rule ATrue (UNIF1 (Var R x1)) eps (UNIF1 (Var R x2))
                 (fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat x1)),(m2 (of_nat x2)) with
                                  | (v1, (er11, er12)),(v2, (er21, er22)) =>
                                    forall l r,
                                      Rlt l v1 -> Rlt v1 r -> Rlt (Rmult (Ropp eps) l) v2 -> Rlt v2 (Rmult (Ropp eps) l)
                                  end
                 end)
  | H_Null  x1 x2:
hoare_rule ATrue (UNIF2 (Var R x1)) 0 (UNIF2 (Var R x2))
(fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat x1)),(m2 (of_nat x2)) with
                                  | (v1, (er11, er12)),(v2, (er21, er22)) =>
                                      v1 = v2
                                  end
                 end)
    .

