(**
  Formalization of the base exprression language for the flover framework
 **)
From Coq
     Require Import  Structures.Orders Recdef.


From Coq
     Require Import QArith.QArith Structures.Orders Recdef.

From Snapv
      Require Export Expressions.

(**
  Expressions will use binary operators.
  Define them first
**)

(**
  Define exprressions commands over some value type V for expression.
  Will ease reasoning about different instantiations later.
**)
Inductive command (V: Type) : Type :=
  (* VAR X*)
    ASGN : expr V -> expr V -> command V
  | SEQ : command V -> command V -> command V
  (* VAR X*)
  | UNIF1 : expr V -> command V
  | UNIF2 : expr V -> command V
  | SKIP : command V.





