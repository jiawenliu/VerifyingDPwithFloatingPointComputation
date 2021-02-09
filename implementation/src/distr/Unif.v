From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq
  ssrint rat ssralg ssrnum bigop path fintype.

From Gappa Require Import Gappa_tactic.

From Snapv.lib
     Require Export MachineType.

From Snapv Require Import Environments.

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



(* The uniform distribution ranging over fixed floating point number from 0 to 1*)

Definition F2R f := Num f.


Definition floats_01 : {fset float64} := fset (map (fun x => R2F64 (Rmult (Rpower 2 ( Ropp 53)) (INR x)))(iota 0 (2^53))).

Definition floats_pair_01_eps (eps : R) : {fset (float64 * float64)} :=
  fset (map (fun x => (R2F64 (Rmult (Rpower 2 ( Ropp 53)) (INR x)), R2F64 (Rmult (Rmult (Rpower 2 ( Ropp 53)) (INR x)) (exp (eps))))) (iota 0 (2^53))).

Definition floats_pair_01_R (eps : R) : {fset (float64 * float64)} :=
  fset_filter (fun xy => (rle (F2R xy.2) 1)) (floats_pair_01_eps eps).

Definition floats_pair_01_L (eps : R) : {fset  (float64 * float64)} :=
  fset_filter (fun xy => (rle (exp (Ropp eps))  (F2R xy.1)) )
              (fset (map (fun x => (R2F64 (Rmult (Rpower 2 ( Ropp 53)) (INR x)), R2F64 1%R )) (iota 0 (2^53)))).

Definition floats_pair_01_eps01 (eps :R) : {fset  (float64 * float64)} :=
  fsetU (floats_pair_01_R eps) (floats_pair_01_L eps).



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



Definition unif_epsR_mass eps xy : rat :=
  if (xy \in  (floats_pair_01_R eps))
  then                        
      (fracq ((Posz 1), (Posz (2^53))))
  else
    if (xy \in  (floats_pair_01_L eps))
    then
      (fracq ((Posz 1), (Posz (2^53))))
  else zeroq
.

Definition unif_epsL_mass eps xy: rat :=
  if (xy \in  (floats_pair_01_eps01 eps) )
  then
    (fracq ((Posz 1), (Posz (2^53))))
  else zeroq
.

Lemma unif_epsR_subproof1 eps xy : (xy \in  (floats_pair_01_eps01 eps) ) 
-> zeroq <= (unif_epsR_mass eps xy).
Proof. 
Admitted.


Lemma unif_epsR_subproof2 eps: \sum_(xy <-  (floats_pair_01_eps01 eps) ) unif_epsR_mass eps xy = 1.
Proof. 
Admitted.

Definition unif_epsR eps :=
  mkprob (@unif_epsR_subproof1 eps) (unif_epsR_subproof2 eps).


Definition unif_epsL eps :=
  mkprob (@unif_epsR_subproof1 eps) (unif_epsR_subproof2 eps).


Lemma unif_epsR_samplR eps :
unif_01 = sample: x <- unif_epsR eps; (dirac \o snd) x.
Proof. 
Admitted.


Lemma unif_epsL_samplL eps :
unif_01 = sample: x <- unif_epsR eps; (dirac \o fst) x.
Proof. 
Admitted.


Lemma unif_epsR_supp eps : forall xy,
  xy \in supp (unif_epsR eps)
         -> forall l r : R,
      (Rle l ((F2R xy.1), (F2R xy.2)).1 /\ Rle ((F2R xy.1),  (F2R xy.2)).1 r) -> 
      (Rle (eps * l) ((F2R xy.1),  (F2R xy.2)).2 /\ Rle ((F2R xy.1),  (F2R xy.2)).2 (eps * r)).
Proof.
Admitted.


Lemma unif_epsL_supp eps : forall xy,
  xy \in supp (unif_epsL eps)
         -> forall l r : R,
      (Rle l ( (F2R xy.1),  (F2R xy.2)).1
      /\ Rle ( (F2R xy.1),  (F2R xy.2)).1 r) -> 
      (Rle (eps * l) ( (F2R xy.1),  (F2R xy.2)).2 /\ Rle ((F2R xy.1),  (F2R xy.2)).2 (eps * r)).
Proof.
Admitted.

Lemma unif_epsL_div eps epsD: forall xy,
    fle (fsub (Q2F ( (unif_epsL eps) xy)) (fmult (f64exp (R2F64 epsD)) (Q2F ( (unif_epsR eps) xy)))) {| MachineType.Num := 0 |}.

Proof.
Admitted.


Lemma unif_epsR_div eps epsD: forall xy,
    fle (fsub (Q2F ( (unif_epsR eps) xy)) (fmult (f64exp (R2F64 epsD)) (Q2F ( (unif_epsL eps) xy)))) {| MachineType.Num := 0 |}.

Proof.
Admitted.


(* The uniform distribution ranging over sign of + and -*)

Definition signs : {fset float64} := fset ([:: (R2F64 (-1)%R); (R2F64 1%R) ]).

Definition unif_sign_mass x: rat :=
  if ((F2R x) == 1%R)
  then (fracq (1, (Posz 2)))
  else if ( (F2R x) == (-1)%R)
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
