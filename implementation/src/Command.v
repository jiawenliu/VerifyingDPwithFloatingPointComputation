(**
  Formalization of the while language for verfication framework.
 **)

From Snapv
      Require Export Expressions.

(**
  Define exprressions commands over some value type V for expression.
  Will ease reasoning about different instantiations later.
**)
Inductive command : Type :=
  (* VAR X*)
    ASGN : expr -> expr -> command
  | SEQ : command -> command -> command
  (* VAR X*)
  | UNIF1 : expr -> command
  | UNIF2 : expr -> command
  | SKIP : command.





