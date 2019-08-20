Set Implicit Arguments.
Require Export Arith.
Require Import Coq.Classes.SetoidTactics.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Classes.Morphisms.

Open Local Scope signature_scope.

Lemma beq_nat_neq: ∀ x y : nat, x <> y → false = beq_nat x y.

Lemma if_beq_nat_nat_eq_dec : ∀ A (x y:nat) (a b:A),
  (if beq_nat x y then a else b) = if eq_nat_dec x y then a else b.

Definition ifte A (test:bool) (thn els:A) := if test then thn else els.

Add Parametric Morphism (A:Type) : (@ifte A)
  with signature (eq ⇒eq ⇒ eq ⇒ eq) as ifte_morphism1.

Add Parametric Morphism (A:Type) x : (@ifte A x)
  with signature (eq ⇒ eq ⇒ eq) as ifte_morphism2.

Add Parametric Morphism (A:Type) x y : (@ifte A x y)
  with signature (eq ⇒ eq) as ifte_morphism3.
