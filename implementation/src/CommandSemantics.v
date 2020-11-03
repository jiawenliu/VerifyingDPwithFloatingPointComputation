(**
  Formalization of the base exprression language for the flover framework
 **)
Require Import Coq.Strings.Ascii Coq.Strings.BinaryString.

From Coq
     Require Import  Structures.Orders Recdef.


From Coq
     Require Import QArith.QArith Structures.Orders Recdef.

From Snapv.Infra
     Require Import RealRationalProps RationalSimps Ltacs.

From Snapv.Infra
     Require Export Abbrevs NatSet MachineType.

From Snapv
     Require Import Command ExpressionTransitions.

From Snapv Require Import Maps.

Definition state := total_map (R * (R * R)).

Open Scope R_scope.

Inductive ptbdir : Type := Down | Up.

Definition perturb (e: R) (delta: R) (dir: ptbdir) :  R :=
  match dir with
  (* The Real-type has no error *)
  |Down =>  ( e * (1 + delta))
  (* Fixed-point numbers have an absolute error *)
  |Up => ( e / (1 + delta))
  end.

Hint Unfold perturb.

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


Inductive trans_com (E : trs_env) (delta : R)
  :(command R) -> (trs_env) -> Prop :=
| Seq_trans c1 c2 E1 E2:
    trans_com E delta c1 E1 -> 
    trans_com E1 delta c2 E2 -> 
    trans_com E delta (SEQ c1 c2) E2
| Asgn_trans x e v er1 er2:
    trans_expr E delta e (v, (er1, er2)) ->
    trans_com E delta (ASGN (Var R x) e) ((t_update E (of_nat x) (v, (er1, er2)))) (*(E & {(of_nat x) --> (v, (er1, er2)) })*)
| Sample_trans x e1 e2 v er1 er2:
    trans_expr E delta e1 (v, (er1, er2)) ->
    er1 = er2 -> v = er1 ->
    trans_com E delta (SAMPLE e1 e2) (t_update E (of_nat x) (v, (er1, er2))) (*(E & { sx --> (v, (er1, er2))}) *)
| Skip_trans:
  trans_com E delta (SKIP R) E
.


Close Scope R_scope.

