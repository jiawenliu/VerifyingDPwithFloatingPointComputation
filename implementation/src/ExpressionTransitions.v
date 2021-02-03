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


Definition fl := R2F.

Definition fl64 := R2F64.

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

Hint Unfold perturb : core.

(**
Define expression evaluation relation 
The result value exprresses float computations according to the IEEE standard,
using a perturbation of the real valued computation by (1 + eta), where
|eta| <= machine epsilon.
 **)

Definition eta := 0.00001%R.


Fixpoint expr_eval  (E : state) (e: expr)
  : float64 * err :=
    match e with
    | Var x => appf E (of_nat x)
    | Const c => 
    if (rle (fl c) c) then 
    if (rle c 0) then 
    ((fl64 c), (perturb eta (c) Up, perturb eta (c)  Down))
    else
    ((fl64 c), (perturb eta (c) Down, perturb eta (c)  Up))
    else
    ((fl64 c), (c, c))
    |Unop op e =>
       let (v, err) := (expr_eval E e) in
       let (er1, er2) := err in
    if (rle 0 (F2R v))
     then
        ((evalfUnop op v), 
         (perturb eta (evalRUnop op er1) Down, 
          perturb eta (evalRUnop op er2) Up))
     else
       ((evalfUnop op v), 
         (perturb eta (evalRUnop op er1)  Up, 
          perturb eta (evalRUnop op er2)  Down))
    | Binop op e1 e2 =>
      match op with
      | Plus
      | Expressions.Sub
        => let (v1, err1) := (expr_eval  E e1) in
           let (er1_l, er1_u) := err1 in
           let (v2, err2) := (expr_eval  E e2) in
           let (er2_l, er2_u) := err1 in
           let v := (evalfBinop op v1 v2) in
           if (rle 0 (F2R v)) then
             (v, (perturb eta (evalRBinop op er1_l er2_l)  Down, 
                     perturb eta (evalRBinop op er1_u er2_u)  Up))
           else
             (v, (perturb eta (evalRBinop op er1_l er2_l) Up, 
                     perturb eta (evalRBinop op er1_u er2_u) Down)) 
      | Mult
      | Div
        =>let (v1, err1) := (expr_eval  E e1) in
           let (er1_l, er1_u) := err1 in
           let (v2, err2) := (expr_eval  E e2) in
           let (er2_l, er2_u) := err1 in
           let v := (evalfBinop op v1 v2) in
           if (rle 0 (F2R v1)) && (rle 0 (F2R v2)) then
               (v, 
                (perturb eta (evalRBinop op er1_l er2_l) Down, 
                 perturb eta (evalRBinop op er1_u er2_u) Up))
           else
             if  (rle 0 (F2R v2)) then
               (v, 
                (perturb eta (evalRBinop op er1_l er2_u)  Up, 
                 perturb eta (evalRBinop op er1_u er2_l) Down))
             else
               if (rle 0 (F2R v1)) then
                 (v, 
                  (perturb eta (evalRBinop op er1_u er2_l) Up, 
                   perturb eta (evalRBinop op er1_l er2_u) Down))
               else
                 (v, 
                  (perturb eta (evalRBinop op er1_u er2_u) Down, 
                   perturb eta (evalRBinop op er1_l er2_l) Up))
      | Clamp
      | Round
        => let (v1, err1) := (expr_eval  E e1) in
           let (er1_l, er1_u) := err1 in
           let (v2, err2) := (expr_eval  E e2) in
           let (er2_l, er2_u) := err1 in
           let v := (evalfBinop op v1 v2) in
           (v, ((evalRBinop op er1_l er2_l), (evalRBinop op er1_u er2_u)))
             end                      
    end
  .

Lemma round_eqV : forall (E : state) y v Lam,
(rle ( F2R (E (of_nat y)).1) (v + Lam / 2)) /\ (rle (v - Lam / 2) (F2R (E (of_nat y)).1))
<-> 
   ((F2R (expr_eval E (Binop Round (Const Lam) (Var y))).1) = v) .
Proof. 
  Admitted.


  
Inductive trans_expr (eta : R) (E : state) 
  :(expr) -> float64 * err -> Prop :=
| Var_load x v er1 er2:
    appf E (of_nat x) = (v, (er1, er2)) ->
    trans_expr eta E (Var x) (v, (er1, er2))
| Const_lt_zero c:
    ~ (fl c = c) -> c < 0 ->
    trans_expr eta E   (Const c) 
   (fl64 c, (perturb eta (c)  Up, 
        perturb eta (c)  Down))
| Const_gt_zero c :
    ~ fl c = c -> 0 <= c ->
    trans_expr eta E  (Const c) 
    (fl64 c, (perturb eta (c)  Down, 
        perturb eta (c)  Up))
| Const_eq c :
    fl c = c -> 
    trans_expr eta E (Const c) 
    (fl64 c, (c, c))
| Unop_gt_zero e v op er1 er2:
    (F2R (evalfUnop op v)) > 0 -> 
    trans_expr eta E e (v, (er1, er2)) ->
    trans_expr eta E (Unop op e) 
    ((evalfUnop op v), 
      (perturb eta (evalRUnop op er1)  Down, 
        perturb eta (evalRUnop op er2) Up)) 
| Unop_lt_zero e v op er1 er2:
    (F2R (evalfUnop op v)) < 0 -> 
    trans_expr eta E  e (v, (er1, er2)) ->
    trans_expr eta E  (Unop Neg e) 
    (evalfUnop op v, 
      (perturb eta (evalRUnop op er1)  Up, 
        perturb eta (evalRUnop op er2)  Down)) 

| Binop_PSRC_gt0 op e1 e2 v1 v2 er1_l er1_u er2_l er2_u v:
    (evalfBinop op v1 v2) = v ->
    0 <= (F2R v) ->
    trans_expr eta E  e1 (v1, (er1_l, er1_u)) ->
    trans_expr eta E  e2 (v2, (er2_l, er2_u)) ->
    ((op = Plus) \/ (op = Expressions.Sub) \/ (op = Round) \/ (op = Clamp)) ->
    trans_expr eta E  (Binop op e1 e2) 
    (v, 
      (perturb eta (evalRBinop op er1_l er2_l)  Down, 
        perturb eta (evalRBinop op er1_u er2_u)  Up)) 
| Binop_PSRC_lt0 op e1 e2 v1 v2 er1_l er1_u er2_l er2_u v:
    (evalfBinop op v1 v2) = v ->
    (F2R v) < 0 ->
    trans_expr eta E e1 (v1, (er1_l, er1_u)) ->
    trans_expr eta E e2 (v2, (er2_l, er2_u)) ->
    ((op = Plus) \/ (op = Expressions.Sub) \/ (op = Round) \/ (op = Clamp)) ->
    trans_expr eta E (Binop op e1 e2) 
    (v, 
      (perturb eta (evalRBinop op er1_l er2_l) Up, 
        perturb eta (evalRBinop op er1_u er2_u) Down)) 
| Binop_MD_ltlt op e1 e2 v1 v2 er1_l er1_u er2_l er2_u v:
    (evalfBinop op v1 v2) = v ->
    (F2R v1) < 0 /\ (F2R v2) < 0 ->
    trans_expr eta E e1 (v1, (er1_l, er1_u)) ->
    trans_expr eta E  e2 (v2, (er2_l, er2_u)) ->
    ((op = Mult) \/ (op = Div)) ->
    trans_expr eta E (Binop op e1 e2) 
    (v, 
      (perturb eta (evalRBinop op er1_u er2_u) Down, 
        perturb eta (evalRBinop op er1_l er2_l) Up))
| Binop_MD_gtgt op e1 e2 v1 v2 er1_l er1_u er2_l er2_u v:
    (evalfBinop op v1 v2) = v ->
    0 <=  (F2R v1) /\ 0 <= (F2R v2) ->
    trans_expr eta E e1 (v1, (er1_l, er1_u)) ->
    trans_expr eta E e2 (v2, (er2_l, er2_u)) ->
    ((op = Mult) \/ (op = Div)) ->
    trans_expr eta E (Binop op e1 e2) 
    (v, 
      (perturb eta (evalRBinop op er1_l er2_l) Down, 
        perturb eta (evalRBinop op er1_u er2_u) Up))
| Binop_MD_ltgt op e1 e2 v1 v2 er1_l er1_u er2_l er2_u v:
    (evalfBinop op v1 v2) = v ->
     (F2R v1) < 0 /\ 0 <= (F2R v2) ->
    trans_expr eta E e1 (v1, (er1_l, er1_u)) ->
    trans_expr eta E e2 (v2, (er2_l, er2_u)) ->
    ((op = Mult) \/ (op = Div)) ->
    trans_expr eta E (Binop op e1 e2) 
    (v, 
      (perturb eta (evalRBinop op er1_l er2_u)  Up, 
        perturb eta (evalRBinop op er1_u er2_l) Down)) 
| Binop_MD_gtlt op e1 e2 v1 v2 er1_l er1_u er2_l er2_u v:
    (evalfBinop op v1 v2) = v ->
    0 <=  (F2R v1) /\ (F2R v2) < 0 ->
    trans_expr eta E e1 (v1, (er1_l, er1_u)) ->
    trans_expr eta E e2 (v2, (er2_l, er2_u)) ->
    ((op = Mult) \/ (op = Div)) ->
    trans_expr eta E (Binop  op e1 e2) 
    (v, 
      (perturb eta (evalRBinop op er1_u er2_l) Up, 
        perturb eta (evalRBinop op er1_l er2_u) Down))
| Binop_ClampRound op e1 e2 v1 v2 er1_l er1_u er2_l er2_u v:
    (evalfBinop op v1 v2) = v ->
    trans_expr eta E e1 (v1, (er1_l, er1_u)) ->
    trans_expr eta E e2 (v2, (er2_l, er2_u)) ->
    ((op = Clamp) \/ (op = Round)) ->
    trans_expr eta E (Binop op e1 e2) 
    (v, ((evalRBinop op er1_l er2_l), (evalRBinop op er1_u er2_u)))
.

Lemma round_eq : forall v1 v Lam eta E,
(rle v1 ( (F2R v) + Lam/2)) /\ (rle ( (F2R v) - Lam/2) v1)
-> 
  trans_expr eta E (Binop Round (Const Lam) (Const v1)) (v, ((F2R v), (F2R v))).
Proof. 
  Admitted.


Close Scope R_scope.

Hint Constructors trans_expr : core.

(** *)
(*   Show some simpler (more general) rule lemmata *)
(* **)

