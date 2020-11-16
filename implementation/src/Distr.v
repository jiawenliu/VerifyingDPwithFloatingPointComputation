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
     Require Import Command ExpressionTransitions.

From Snapv Require Import Maps.


From Snapv.aprhl Require Import Extra Prob.

From Flocq Require Import Core Bracket Round Operations Div Sqrt.




Open Scope R_scope.

Inductive  distr_e (V:Type) : Type :=
| UNIFR: V -> V -> distr_e V
| UNIFS: V -> distr_e V.

(* TO RENAME *)
Inductive sem_distr_e (E : trs_env): (distr_e R)
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



Close Scope R_scope.

