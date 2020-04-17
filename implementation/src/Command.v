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
      Require Export Expression

(**
  Expressions will use binary operators.
  Define them first
**)

(**
  Define exprressions commands over some value type V for expression.
  Will ease reasoning about different instantiations later.
**)
Inductive command (V: Type) : Type :=
  Assign : expr V -> expr V -> command V
  | conq : command V -> command V -> command V
  | sample : expr V -> command V.





