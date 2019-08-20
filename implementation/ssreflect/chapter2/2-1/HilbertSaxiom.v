Require Import ssreflect ssrbool.

Section HilbertSaxiom.

Variables A B C : Prop.

Lemma HilbertS : (A -> B -> C) -> (A -> B) -> A -> C.

Proof.
move=> hAiBiC hAiB hA.
move: hAiBiC.apply.by [].by apply: hAiB.Qed.


Hypotheses (hAiBiC : A -> B -> C) (hAiB : A -> B) (hA : A).

Lemma HilbertS2 : C.
Proof.
apply: hAiBiC; first by apply: hA.exact: hAiB.Qed.

Lemma HilbertS3 : C.
Proof. by apply: hAiBiC; last exact: hAiB. Qed.

Check (hAiB hA).

Check (hAiBiC hA).

Check ((hAiBiC hA) (hAiB hA)).

Check hAiBiC hA (hAiB hA).

Lemma HilbertS4 : C.Proof. exact: (hAiBiC _ (hAiB _)). Qed.

Lemma HilbertS5 : C.Proof. exact: hAiBiC (hAiB _). Qed.

Lemma HilbertS6 : C.Proof. exact: HilbertS5. Qed.

Print HilbertS5.Print HilbertS2.Print HilbertS.Check HilbertS.End HilbertSaxiom.Print HilbertS5.

