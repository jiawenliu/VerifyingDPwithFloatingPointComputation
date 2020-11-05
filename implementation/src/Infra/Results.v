From Coq
     Require Import Strings.Ascii Strings.String Lists.List.

Set Implicit Arguments.

Inductive result (rT:Type) : Type :=
  | Succes: rT -> result rT
  | Fail: string -> result rT
  | FailDet: string -> rT -> result rT.

Definition injectResult (rT:Type) (r:result rT) :=
  match r with
  | Succes _ => true
  | Fail _ _ => false
  | FailDet _ _ => false
  end.

Coercion injectResult : result >-> bool.
