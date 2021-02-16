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

Definition F2R f := Num f.

Definition env := state.

Definition err : Type :=  (R * R).

Definition distr_m := { prob env }.

Definition unit_E  (E : env) := dirac E.


Inductive trans_com (eta : R) (E : env) 
  :(command) -> distr_m  -> Prop :=
| Asgn_trans x e v er1 er2:
    trans_expr eta E e (v, (er1, er2)) -> 
    trans_com eta E  (ASGN (Var x) e) (unit_E ((upd E (of_nat x) (v, (er1, er2)))))
| Skip_trans:
  trans_com eta E  (SKIP) (unit_E E)
| Unif01_trans x:    
  trans_com eta E  (UNIF1 (Var x))
              (sample: v <- unif_01; dirac ((upd E (of_nat x) (v, ((F2R v), (F2R v)))) ))
| Sample_trans x:
     trans_com eta E (UNIF2 (Var x))
              (sample: v <- unif_sign; dirac ((upd E (of_nat x) (v, ((F2R v), (F2R v)))) ))
| Seq_trans c1 c2 distr1 f:
    trans_com eta E  c1 distr1 ->
    (* ***** abstract function f takes care of the transformation from m \in distr1 into distr2 ****** *)
    (forall m, trans_com eta m c2 (f m)) -> 
    trans_com eta E (SEQ c1 c2) (sample distr1 f)
    
.

Definition semantics_sound (st: env) x : Prop :=
  match (st x) with
  | (v, (er1, er2)) => (rle er1 (F2R v)) /\ (Rle (F2R v) er2)
  end.
 
(*The semantics defined for commands as functions*)


Fixpoint com_eval (E : env) (c : command) : (distr_m):=
  match c with
  | SKIP => dirac E
  | (ASGN (Var x) e) =>
    dirac (upd E (of_nat x) (expr_eval' E e))
  | (UNIF1 (Var x)) =>
    (sample: v <- unif_01; dirac ((upd E (of_nat x) (v, ((F2R v), (F2R v)))) ))
    (* S T -> {Prob T} -> (fun: MEM -> {Prob T})*)
  | (UNIF2 (Var x)) =>
    (sample: v <- unif_sign; dirac ((upd E (of_nat x) (v, ((F2R v), (F2R v)))) ))
  | SEQ c1 c2 =>
    (sample: E1 <- (com_eval E c1); (com_eval E1 c2))
    (* {Prob MEM} -> (fun: MEM -> {Prob T})*)
  | _ => dirac E
  end
  .

Close Scope R_scope.

