Require Import ssreflect ssrbool.



Section Equality.

Variable f : nat -> nat.

Hypothesis f00 : f 0 = 0.

Lemma fkk : forall k, k = 0 -> f k = k.
Proof.
move=> k k0.
by rewrite k0.

Qed.

Lemma fkk2 : forall k, k = 0 -> f k = k.
Proof. 
by move=> k ->. 
Qed.

Variable f10 : f 1 = f 0.
Lemma ff10 : f (f 1) = 0.
Proof. by rewrite f10 f00. 
Qed.


Variables (D : eqType) (x y : D).

Lemma eq_prop_bool : x = y -> x == y.

Proof. by move/eqP. 
Qed.

Lemma eq_bool_prop : x == y -> x = y.

Proof. by move/eqP. 
Qed.

End Equality.