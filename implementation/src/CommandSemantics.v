(**
  Formalization of the base exprression language for the flover framework
 **)
Require Import Coq.Strings.Ascii Coq.Strings.BinaryString.

From Coq
     Require Import  Structures.Orders Recdef.


From Coq
     Require Import QArith.QArith Structures.Orders Recdef.

From Coq.QArith
     Require Export Qreals.

From Coq
     Require Import Reals.Reals.

From mathcomp Require Import
     ssreflect ssrfun ssrbool eqtype ssrnat choice seq
     bigop path   .


From Snapv
     Require Export MachineType.

From Snapv
     Require Import Command ExpressionTransitions Environments Maps.

From Snapv.distr Require Import Extra Prob.

From Flocq Require Import Core Bracket Round Operations Div Sqrt.

From extructures Require Import ord fset fmap ffun.


Open Scope R_scope.

Inductive ptbdir : Type := Down | Up.


Definition env := state.

(* F = fl(R) *)
Definition fl (r : R) := r
  .

Definition err : Type :=  (R * R).

Definition distr_m := { prob env }.


(* TODO: Be Specific *)
Inductive  distr_e (V:Type) : Type :=
| UNIFR: V -> V -> distr_e V
| UNIFS: V -> distr_e V.

(* TO RENAME  SUPP E distre (R * R * R) => (R* R*R)  \in distre *)
Inductive sem_distr_e (E : env): (distr_e R)
 -> (R * (R * R)) -> Prop :=
| UnifR_sem v v1 v2 er1 er2:
    er1 = er2 -> v = er1 ->
  v1 <= v -> v <= v2 ->
    sem_distr_e E (UNIFR v1 v2) (v, (er1, er2)) (*(E & { sx --> (v, (er1, er2))}) *)
| UnifS_sem v v1 v2 er1 er2:
    er1 = er2 -> v = er1 ->
  v1 <= v <= v2 ->
    sem_distr_e E (UNIFS v1) (v, (er1, er2)) (*(E & { sx --> (v, (er1, er2))}) *)
.


Definition unit_E  (E : env) := dirac E.



Inductive trans_com (E : env) (delta : R)
  :(command R) -> distr_m  -> Prop :=
| Asgn_trans x e v er1 er2:
    trans_expr E delta e (v, (er1, er2)) -> 
    trans_com E delta (ASGN (Var R x) e) (unit_E ((upd E (of_nat x) (v, (er1, er2))))) (*(E & {(of_nat x) --> (v, (er1, er2)) })*)
| Skip_trans:
  trans_com E delta (SKIP R) (unit_E E)
| Unif01_trans x v er1 er2:
     sem_distr_e E (UNIFR 0 1) (v, (er1, er2)) ->
     trans_com E delta (UNIF1 (Var R x))
               (unit_E (upd E (of_nat x) (v, (er1, er2)))) (*(E & { sx --> (v, (er1, er2))}) *)
| Sample_trans x v er1 er2:
     sem_distr_e E (UNIFS 1) (v, (er1, er2)) ->
    trans_com E delta (UNIF2 (Var R x))
              (unit_E (upd E (of_nat x) (v, (er1, er2)))) (*(E & { sx --> (v, (er1, er2))}) *)
| Seq_trans c1 c2 E1 distr1 distr2:
    trans_com E delta c1 distr1 ->
     (E1 \in supp distr1) ->
    trans_com E1 delta c2 distr2 -> 
    trans_com E delta (SEQ c1 c2) distr2
.


Close Scope R_scope.

