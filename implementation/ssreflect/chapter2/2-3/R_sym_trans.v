Require Import ssreflect ssrbool.

Section R_sym_trans.

Variables (D : Type) (R : D -> D -> Prop).

Hypothesis R_sym : forall x y, R x y -> R y x.

Hypothesis R_trans : forall x y z, R x y -> R y z -> R x z.

Lemma refl_if : forall x : D, (exists y, R x y) -> R x x.

Proof.

move=> x [y Rxy].

by apply: R_trans _ (R_sym _ y _).

Qed.

End R_sym_trans.