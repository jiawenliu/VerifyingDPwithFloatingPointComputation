From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
From mathcomp Require Import seq choice.
From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun.
Require Import Coq.Reals.Reals.
Require Import Coq.Strings.String.
From Snapv.lib Require Import MachineType.
Require Import Coq.micromega.Lra Coq.micromega.Lia.

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
  
-move=> x y.
 case: (Rle_dec x y) (Rle_dec y x).
 move =>  [xy|//] RD.
 split.
 move => nxy Rd.
 
 destruct Rd.
 rewrite orbT //.
 lra.
Qed.

Definition R_ordMixin := OrdMixin rleP.
Canonical R_ordType := OrdType R R_ordMixin.

Lemma RleP (x y : R) : reflect (Rle x y) (x <= y)%ord.
Proof.
by rewrite /Ord.leq /= /rle; case: Rle_dec => ? /=; constructor.
Qed.

(** With all these definitions in place, we can define states as finite
    functions, and Coq will be able to figure out that they form an ordered type
    (because their keys and values are ordered).

    If [f : T -> S], the type [ffun f] contains functions that are equal to [f]
    in all but finitely many inputs. When [f] is a constant function [fun _ =>
    y], this means that almost all outputs of a finite function are equal to [y]

 *)
Axiom feq_req_ref : forall x y,  reflect (x = y) (req (Num x) (Num y)).



Definition feq x y : bool := Req_EM_T (Num x) (Num y).
Lemma feqP : Equality.axiom feq.
Proof.
  move => x y.
  unfold feq.

  apply feq_req_ref.
Qed.
Definition F_eqMixin := EqMixin feqP.
Canonical F_eqType := EqType float64 F_eqMixin.

(** We also need to show that real numbers satisfy a choice principle.  This is
not part of the real number axioms, so I am going to postulate it
here. (Alternatively, we could show that this follows from the standard axiom of
choice included in Coq's standard library.) *)

Axiom F_choiceMixin : choiceMixin float64.
Canonical F_choiceType := ChoiceType float64 F_choiceMixin.

(** Finally, we can show that the reals are an ordered type. *)

Definition fle x y : bool := Rle_dec  (Num x) (Num y).
Lemma fleP : Ord.axioms fle.
Proof.
rewrite /fle; split.
- move=> x; exact/(introT (sumboolP _))/Rle_refl.
- move=> y x z.
  case: (Rle_dec  (Num x) (Num y)) (Rle_dec  (Num y) (Num z)) => [xy|//] [yz|//] _ _.
  apply/(introT (sumboolP _)). exact: Rle_trans xy yz.
- move=> x y.
  case: (Rle_dec  (Num x) (Num y)) (Rle_dec (Num y) (Num x)) => [xy|//] [yx|//] _.
  rewrite feq_req.
  exact: Rle_antisym.
-  move=> x y.
    case:  (Rle_dec  (Num x) (Num y)) (Rle_dec (Num y) (Num x)).
 move =>  [xy|//] RD.
 split.
 move => nxy Rd.
 
 destruct Rd.
 rewrite orbT //.
 lra.
Qed.

Definition F_ordMixin := OrdMixin fleP.
Canonical F_ordType := OrdType float64 F_ordMixin.


Notation state := (ffun (fun v : string => ((F64 0%R), (0%R, 0%R)))).
