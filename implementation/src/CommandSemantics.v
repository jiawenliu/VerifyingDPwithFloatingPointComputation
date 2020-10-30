(**
  Formalization of the base exprression language for the flover framework
 **)
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
Definition trs_env := fun (x : nat) => R * (R * R).

Definition fl (r : R) := r
  .


Definition err :=  R *  R.

Inductive trans_com (E : trs_env) (delta : R)
  :(command R) -> (trs_env) -> Prop :=
| Asgn_trans (ASGN x e) :
  trans_expr E delta e (v, (er1, er2)) ->
    trans_com E delta (Var R x) (fun x (v, (er1, er2)))

.


Close Scope R_scope.

