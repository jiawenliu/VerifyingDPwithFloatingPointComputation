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
     Require Import Command ExpressionTransitions Environments.

From Snapv.distr Require Import Extra Prob Unif.

From Flocq Require Import Core Bracket Round Operations Div Sqrt.

From extructures Require Import ord fset fmap ffun.


Open Scope R_scope.

Definition env := state.

Definition err : Type :=  (R * R).

Definition distr_m := { prob env }.

Definition unit_E  (E : env) := dirac E.

Definition do_sample d : {prob env} :=
 sample: e <- d;
 dirac e. 

(* is_sample d E :  E \in supp d *)
Definition is_sample (d: {prob env}) (E:env) : Prop :=
  E \in supp (do_sample d).



Inductive trans_com (eta : R) (E : env) 
  :(command) -> distr_m  -> Prop :=
| Asgn_trans x e v er1 er2:
    trans_expr eta E e (v, (er1, er2)) -> 
    trans_com eta E  (ASGN (Var x) e) (unit_E ((upd E (of_nat x) (v, (er1, er2)))))
| Skip_trans:
  trans_com eta E  (SKIP) (unit_E E)
| Unif01_trans x:    
  trans_com eta E  (UNIF1 (Var x))
              (sample: v <- unif_01; dirac ((upd E (of_nat x) (v, (v, v))) ))
| Sample_trans x:
     trans_com eta E (UNIF2 (Var x))
              (sample: v <- unif_sign; dirac ((upd E (of_nat x) (v, (v, v))) ))
| Seq_trans c1 c2 E1 distr1 distr2:
    trans_com eta E  c1 distr1 ->
    (* (sample: v <- distr1; trans_com eta v c2 ) ->*)
    trans_com eta E1 c2 distr2 -> 
    trans_com eta E (SEQ c1 c2) distr2
    
.


Close Scope R_scope.

