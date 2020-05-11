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
     Require Import Command Expressions.

(**
  Expressions will use binary operators.
  Define them first
**)

Inductive eval_command (E : env) (C : command)

(**
  Next define an evaluation function for binary operators on reals.
  Errors are added on the exprression evaluation level later.
 **)
  