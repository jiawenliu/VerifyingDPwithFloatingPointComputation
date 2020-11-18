From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
From mathcomp Require Import seq choice.
From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun.
Require Import Coq.Reals.Reals.
Require Import Coq.Strings.String.

(** First, we need to show that real numbers have an equality operator.  This
follows from the axioms on reals. *)

Definition req x y : bool := Req_EM_T x y.
Lemma reqP : Equality.axiom req.
Proof. move=> ??; exact: sumboolP. Qed.
Definition R_eqMixin := EqMixin reqP.
Canonical R_eqType := EqType R R_eqMixin.

(** We also need to show that real numbers satisfy a choice principle.  This is
not part of the real number axioms, so I am going to postulate it
here. (Alternatively, we could show that this follows from the standard axiom of
choice included in Coq's standard library.) *)

Axiom R_choiceMixin : choiceMixin R.
Canonical R_choiceType := ChoiceType R R_choiceMixin.

(** Finally, we can show that the reals are an ordered type. *)

Definition rle x y : bool := Rle_dec x y.
Lemma rleP : Ord.axioms rle.
Proof.
rewrite /rle; split.
- move=> x; exact/(introT (sumboolP _))/Rle_refl.
- move=> y x z.
  case: (Rle_dec x y) (Rle_dec y z) => [xy|//] [yz|//] _ _.
  apply/(introT (sumboolP _)). exact: Rle_trans xy yz.
- move=> x y.
  case: (Rle_dec x y) (Rle_dec y x) => [xy|//] [yx|//] _.
  exact: Rle_antisym.
- (* Exercise: prove this! *)
  admit.
Admitted.
Definition R_ordMixin := OrdMixin rleP.
Canonical R_ordType := OrdType R R_ordMixin.

(** With all these definitions in place, we can define states as finite
    functions, and Coq will be able to figure out that they form an ordered type
    (because their keys and values are ordered).

    If [f : T -> S], the type [ffun f] contains functions that are equal to [f]
    in all but finitely many inputs. When [f] is a constant function [fun _ =>
    y], this means that almost all outputs of a finite function are equal to [y]

*)

Notation state := (ffun (fun v : string => (0%R, (0%R, 0%R)))).

Check [ordType of state].
