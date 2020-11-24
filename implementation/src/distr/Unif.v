From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq
  ssrint rat ssralg ssrnum bigop path.

From Gappa Require Import Gappa_tactic.

From Snapv
     Require Export MachineType.

From Snapv.distr Require Import Extra Prob.

From Flocq Require Import Core Bracket Round Operations Div Sqrt.

From extructures Require Import ord fset fmap ffun.


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


Lemma radix_subproof1 : (2 <=? 2)%Z = true.
Proof.
Admitted.


Definition FT : Type := (float radix2).


(* The uniform distribution ranging over fixed floating point number from 0 to 1*)

(*
Definition unif_01_mass x: rat :=
  if (rle 0 x)
  then if rle x 1
       then 1/(2^53)
       else 0      
  else 0        
.


Lemma unif_01_subproof1 x : 0 <= unif_01_mass.
Proof. by rewrite /unif_01_mass; case: eq_op. Qed.

Lemma unif_01_subproof2 x : \sum_(x) unif_01_mass x = 1.
Proof.
admitted.
Qed.


Definition unif_01 :=
  mkprob (@unif_01_subproof1 x) (unif_01_subproof2 x).

 *)

(* The uniform distribution ranging over sign of + and -*)

(*
Definition unif_sign_mass x: rat :=
  if (x = 1%R)
  then 0.5
  else if (x = -1%R)
       then 0.5
       else 0        
.

Lemma unif_sign_subproof1 x : 0 <= unif_sign_mass.
Proof. by rewrite /unif_01_mass; case: eq_op. Qed.

Lemma unif_sign_subproof2 x : \sum_(x) unif_sign_mass x = 1.
Proof.
admitted.
Qed.

Definition unif_sign x :=
  mkprob (@unif_sign_subproof1 x) (unif_sign_subproof2 x).

*)

Inductive  distr_e : Type :=
| UNIFR:  distr_e
| UNIFS:  distr_e.

(* TO RENAME *)
Inductive in_supp : (distr_e)
 -> (R * (R * R)) -> Prop :=
| UnifR_supp v er1 er2:
    er1 = er2 -> v = er1 ->
  (Rle 0 v) -> (Rle v 1) ->
   in_supp (UNIFR) (v, (er1, er2)) (*(E & { sx --> (v, (er1, er2))}) *)
| UnifS_supp v  er1 er2:
    er1 = er2 -> v = er1 ->
    v = 1%R ->
    in_supp (UNIFS) (v, (er1, er2)) (*(E & { sx --> (v, (er1, er2))}) *)
.




