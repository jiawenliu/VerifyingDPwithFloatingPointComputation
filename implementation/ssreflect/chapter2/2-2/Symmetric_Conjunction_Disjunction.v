
Require Import ssreflect ssrbool.

Print bool.

Section Symmetric_Conjunction_Disjunction.


Lemma andb_sym : forall A B : bool, A && B -> B && A.

Proof.
case.
by case.
by [].
Qed.

Lemma andb_sym2 : forall A B : bool, A && B -> B && A.Proof. by case; case. Qed.

Lemma andb_sym3 : forall A B : bool, A && B -> B && A.
Proof.
by do 2! case. Qed.

Variables (C D : Prop) (hC : C) (hD : D).

Check (and C D).

Print and.

Check (conj hC hD).

Lemma and_sym : forall A B : Prop, A /\ B -> B /\ A.
Proof.
by move=> A1 B [].
Qed.

Print or.

Lemma or_sym : forall A B : Prop, A \/ B -> B \/ A.
Proof.
by move=> A B [hA| hB];
[apply : or_intror| apply : or_introl].
Qed.

Lemma or_sym2 : forall A B : bool, A \/ B -> B \/ A.Proof. by move=> [] [] AorB; apply/orP; move/orP : AorB. Qed.

End Symmetric_Conjunction_Disjunction.