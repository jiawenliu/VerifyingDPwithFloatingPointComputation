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

From Snapv.distr Require Import Extra Prob Unif.

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



Definition unit_E  (E : env) := dirac E.


Definition do_sample d : {prob state} :=
  sample: e <- d;
 dirac e.

Definition is_sample (d: {prob state}) (E:state) : Prop :=
  E \in supp (do_sample d).



Inductive trans_com (E : env) 
  :(command) -> distr_m  -> Prop :=
| Asgn_trans x e v er1 er2:
    trans_expr E e (v, (er1, er2)) -> 
    trans_com E  (ASGN (Var x) e) (unit_E ((upd E (of_nat x) (v, (er1, er2)))))
| Skip_trans:
  trans_com E  (SKIP) (unit_E E)
| Unif01_trans x v er1 er2:
     in_supp (UNIFR) (v, (er1, er2)) ->
     trans_com E  (UNIF1 (Var x))
               (unit_E (upd E (of_nat x) (v, (er1, er2))))
| Sample_trans x v er1 er2:
     in_supp (UNIFS) (v, (er1, er2)) ->
    trans_com E  (UNIF2 (Var x))
              (unit_E (upd E (of_nat x) (v, (er1, er2)))) 
| Seq_trans c1 c2 E1 distr1 distr2:
    trans_com E  c1 distr1 ->
     is_sample distr1 E1 ->
    trans_com E1  c2 distr2 -> 
    trans_com E  (SEQ c1 c2) distr2
.


Close Scope R_scope.

