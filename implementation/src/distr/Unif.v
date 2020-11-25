From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq
  ssrint rat ssralg ssrnum bigop path fintype.

From Gappa Require Import Gappa_tactic.

From Snapv
     Require Export MachineType.

From Snapv.distr Require Import Extra Prob.

From Flocq Require Import Core Bracket Round Operations Div Sqrt.

From extructures Require Import ord fset fmap ffun.


From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun.
Require Import Coq.Reals.Reals Coq.ZArith.Int.
Require Import Coq.Strings.String.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope fset_scope.

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



Definition FT : Type := (float radix2).





(* The uniform distribution ranging over fixed floating point number from 0 to 1*)

Definition floats_01 : {fset R} := fset (map (fun x => (Rmult (Rpower 2 ( Ropp 53)) (INR x)))(iota 0 (2^53))).


Definition unif_01_mass x: rat :=
  if (x \in floats_01)
  then  (fracq ((Posz 1), (Posz (2^53))))
       else zeroq     
.

Lemma unif_01_subproof1 x : x \in floats_01 ->   zeroq <= (unif_01_mass x).
Proof.
  
  Admitted.
    (* by rewrite /unif_01_mass; case: eq_op. Qed.*)

Lemma unif_01_subproof2 : \sum_(x <- floats_01) unif_01_mass x = 1.
Proof.
  Admitted.


Definition unif_01 :=
  mkprob (@unif_01_subproof1) (unif_01_subproof2).


(* The uniform distribution ranging over sign of + and -*)

Definition signs : {fset R} := fset ([:: (-1)%R; 1%R]).

Definition unif_sign_mass x: rat :=
  if (x == 1%R)
  then (fracq (1, (Posz 2)))
  else if (x == (-1)%R)
       then  (fracq (1, (Posz 2)))
       else 0     
.

Lemma unif_sign_subproof1 x : x \in signs ->  0 <= (unif_sign_mass x).
Proof.
  unfold unif_sign_mass.
  Admitted.
    (*by rewrite /unif_sign_mass; case: eq_op. Qed.*) 

Lemma unif_sign_subproof2 : \sum_(x <- signs) unif_sign_mass x = 1.
Proof.
  Admitted.
(* Qed.*)

Definition unif_sign :=
  mkprob (@unif_sign_subproof1) (unif_sign_subproof2).





Close Scope fset_scope.
Close Scope ring_scope.
