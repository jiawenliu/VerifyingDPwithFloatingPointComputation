(**
  Formalization of the while language for verfication framework.
 **)

From Snapv
      Require Export Expressions.

Declare Scope com_scope.
Delimit Scope com_scope with com.

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

Notation "c1 ;; c2" := (SEQ c1 c2)
  (at level 45, right associativity, format "c1 ;;  c2") : com_scope.

Notation "v ::= e" := (ASGN v e)
  (at level 20, no associativity) : com_scope.
