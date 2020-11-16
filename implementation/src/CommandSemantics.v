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



Definition state := total_map (R * (R * R)).

Open Scope R_scope.

Inductive ptbdir : Type := Down | Up.

(*
Inductive  distr (V:Type) : Type :=
  UNIT: V -> distr V
| UNIFR: V -> V -> distr V
| UNIFS: V -> distr V.
*)


(**
Define expression evaluation relation parametric by an "error" epsilon.
The result value exprresses float computations according to the IEEE standard,
using a perturbation of the real valued computation by (1 + delta), where
|delta| <= machine epsilon.
**)
Definition trs_env := state.

Definition fl (r : R) := r
  .

Definition err : Type :=  (R * R).

Inductive distr_m : Type :=
    UNITM:  trs_env ->  distr_m.

Print  trs_env.

Inductive sem_distr_m : (distr_m) -> ( trs_env)
  -> Prop :=
  Unitm_sem m:
    sem_distr_m (UNITM m) m.


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



  
(* TO RENAME *)
Inductive trans_com (E : trs_env) (delta : R)
  :(command R) -> distr_m  -> Prop :=
| Asgn_trans x e v er1 er2:
    trans_expr E delta e (v, (er1, er2)) ->
    trans_com E delta (ASGN (Var R x) e) (UNITM ((t_update E (of_nat x) (v, (er1, er2))))) (*(E & {(of_nat x) --> (v, (er1, er2)) })*)
| Skip_trans:
  trans_com E delta (SKIP R) (UNITM E)
| Unif01_trans x v er1 er2:
     sem_distr_e E (UNIFR 0 1) (v, (er1, er2)) ->
     trans_com E delta (UNIF01 (Var R x))
               (UNITM (t_update E (of_nat x) (v, (er1, er2)))) (*(E & { sx --> (v, (er1, er2))}) *)
| Sample_trans x v er1 er2:
     sem_distr_e E (UNIFS 1) (v, (er1, er2)) ->
    trans_com E delta (UNIF1 (Var R x))
              (UNITM (t_update E (of_nat x) (v, (er1, er2)))) (*(E & { sx --> (v, (er1, er2))}) *)
| Seq_trans c1 c2 E1 distr1 distr2:
    trans_com E delta c1 distr1 ->
     sem_distr_m distr1 E1 ->
    trans_com E1 delta c2 distr2 -> 
    trans_com E delta (SEQ c1 c2) distr2
.


Close Scope R_scope.

