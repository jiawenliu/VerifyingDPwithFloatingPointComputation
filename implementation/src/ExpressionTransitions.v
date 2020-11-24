Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Decimal Ascii String.
Require Import Coq.Strings.Ascii Coq.Strings.BinaryString.
Import ListNotations.

From Coq
     Require Import Reals.Reals.

From Snapv Require Export Expressions Environments.
From Snapv.distr Require Import Extra Prob.
From Snapv.lib Require Import MachineType.

From extructures Require Import ord fset fmap ffun.

From mathcomp Require Import
     ssreflect ssrfun ssrbool eqtype ssrnat choice seq
     bigop path.

(**
  Define the Transition From the real computation to the Floating Point Computation with Floating point Relative Error
**)
Open Scope R_scope.


Definition fl := R2FFP.


Definition err : Type :=  (R * R).
  (*TO RENAME*)

  Definition env := state.

  (*The machine epsilon under the 64 bits fixed floating point computation*)
  
Inductive ptbdir : Type := Down | Up.

Definition perturb (eta : R) (e: R) (dir: ptbdir) :  R :=
  match dir with
  (* the upper bound of the relative error for Fixed-point computation,
   computed in terms of real number*)
  |Down =>  (e * (1 + eta))
  (* the lower bound of the relative error for Fixed-point computation, 
   computed in terms of real number*)
  |Up => ( e / (1 + eta))
  end.

Hint Unfold perturb.

(**
Define expression evaluation relation 
The result value exprresses float computations according to the IEEE standard,
using a perturbation of the real valued computation by (1 + eta), where
|eta| <= machine epsilon.
 **)



  
Inductive trans_expr (eta : R) (E : state) 
  :(expr) -> R * err -> Prop :=
| Var_load x v er1 er2:
    appf E (of_nat x) = (v, (er1, er2)) ->
    trans_expr eta E (Var x) (v, (er1, er2))
| Const_lt_zero c:
    ~ (fl c = c) -> c < 0 ->
    trans_expr eta E   (Const c) 
   (c, (perturb eta (c) Up, 
        perturb eta (c)  Down))
| Const_gt_zero c :
    ~ fl c = c -> 0 <= c ->
    trans_expr eta E  (Const c) 
    (c, (perturb eta (c)  Down, 
        perturb eta (c)  Up))
| Const_eq c :
    fl c = c -> 
    trans_expr eta E (Const c) 
    (c, (c, c))
| Unop_gt_zero e v op er1 er2:
    (evalUnop op v) > 0 -> 
    trans_expr eta E e (v, (er1, er2)) ->
    trans_expr eta E (Unop Neg e) 
    (fl (evalFUnop Neg v), 
      (perturb eta (evalRUnop op er1)  Down, 
        perturb eta (evalRUnop op er2) Up)) 
| Unop_lt_zero e v op er1 er2:
    (evalFUnop op v) < 0 -> 
    trans_expr eta E  e (v, (er1, er2)) ->
    trans_expr eta E  (Unop Neg e) 
    (evalFUnop op v, 
      (perturb eta (evalRUnop op er1)  Up, 
        perturb eta (evalRUnop op er2)  Down)) 

| Binop_PSRC_gt0 op e1 e2 v1 v2 er1_l er1_u er2_l er2_u v:
    (evalFBinop op v1 v2) = v ->
    0 <= v ->
    trans_expr eta E  e1 (v1, (er1_l, er1_u)) ->
    trans_expr eta E  e2 (v2, (er2_l, er2_u)) ->
    ((op = Plus) \/ (op = Expressions.Sub) \/ (op = Round) \/ (op = Clamp)) ->
    trans_expr eta E  (Binop op e1 e2) 
    (v, 
      (perturb eta (evalRBinop op er1_l er2_l)  Down, 
        perturb eta (evalRBinop op er1_u er2_u)  Up)) 
| Binop_PSRC_lt0 op e1 e2 v1 v2 er1_l er1_u er2_l er2_u v:
    (evalFBinop op v1 v2) = v ->
    v < 0 ->
    trans_expr eta E e1 (v1, (er1_l, er1_u)) ->
    trans_expr eta E e2 (v2, (er2_l, er2_u)) ->
    ((op = Plus) \/ (op = Expressions.Sub) \/ (op = Round) \/ (op = Clamp)) ->
    trans_expr eta E (Binop op e1 e2) 
    (v, 
      (perturb eta (evalRBinop op er1_l er2_l) Up, 
        perturb eta (evalRBinop op er1_u er2_u) Down)) 
| Binop_MD_ltlt op e1 e2 v1 v2 er1_l er1_u er2_l er2_u v:
    (evalFBinop op v1 v2) = v ->
    v1 < 0 /\ v2 < 0 ->
    trans_expr eta E e1 (v1, (er1_l, er1_u)) ->
    trans_expr eta E  e2 (v2, (er2_l, er2_u)) ->
    ((op = Mult) \/ (op = Div)) ->
    trans_expr eta E (Binop op e1 e2) 
    (v, 
      (perturb eta (evalRBinop op er1_u er2_u) Down, 
        perturb eta (evalRBinop op er1_l er2_l) Up))
| Binop_MD_gtgt op e1 e2 v1 v2 er1_l er1_u er2_l er2_u v:
    (evalFBinop op v1 v2) = v ->
    0 <= v1 /\ 0 <= v2 ->
    trans_expr eta E e1 (v1, (er1_l, er1_u)) ->
    trans_expr eta E e2 (v2, (er2_l, er2_u)) ->
    ((op = Mult) \/ (op = Div)) ->
    trans_expr eta E (Binop op e1 e2) 
    (v, 
      (perturb eta (evalRBinop op er1_l er2_l) Down, 
        perturb eta (evalRBinop op er1_u er2_u) Up))
| Binop_MD_ltgt op e1 e2 v1 v2 er1_l er1_u er2_l er2_u v:
    (evalFBinop op v1 v2) = v ->
    v1 < 0 /\ 0 <= v2 ->
    trans_expr eta E e1 (v1, (er1_l, er1_u)) ->
    trans_expr eta E e2 (v2, (er2_l, er2_u)) ->
    ((op = Mult) \/ (op = Div)) ->
    trans_expr eta E (Binop op e1 e2) 
    (v, 
      (perturb eta (evalRBinop op er1_l er2_u)  Up, 
        perturb eta (evalRBinop op er1_u er2_l) Down)) 
| Binop_MD_gtlt op e1 e2 v1 v2 er1_l er1_u er2_l er2_u v:
    (evalFBinop op v1 v2) = v ->
    0 <= v1 /\ v2 < 0 ->
    trans_expr eta E e1 (v1, (er1_l, er1_u)) ->
    trans_expr eta E e2 (v2, (er2_l, er2_u)) ->
    ((op = Mult) \/ (op = Div)) ->
    trans_expr eta E (Binop  op e1 e2) 
    (v, 
      (perturb eta (evalRBinop op er1_u er2_l) Up, 
        perturb eta (evalRBinop op er1_l er2_u) Down))
.


Close Scope R_scope.

Hint Constructors trans_expr.

(** *)
(*   Show some simpler (more general) rule lemmata *)
(* **)

