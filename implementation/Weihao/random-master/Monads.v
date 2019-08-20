(** * Monads.v: Monads for randomized constructions *)

Set Implicit Arguments.
Require Export Uprop.

Module Monad (Univ:Universe).
Module UP := (Univ_prop Univ).
(* begin hide *)
Import Univ.
Import UP.
(* end hide *)
(** ** Definition of monadic operators *)
Definition M (A:Type) := (A -> U) -> U.

Definition unit (A:Type) (x:A) : M A := fun f => f x.

Definition star (A B:Type) (a:M A) (F:A -> M B) : M B := fun f => a (fun x => F x f).

(** ** Properties of monadic operators *)
Lemma law1 : forall (A B:Type) (x:A) (F:A -> M B) (f:B -> U), star (unit x) F f = F x f.
trivial.
Qed.

Lemma law2 :
 forall (A:Type) (a:M A) (f:A -> U), star a (fun x:A => unit x) f = a (fun x:A => f x).
trivial.
Qed.

Lemma law3 :
 forall (A B C:Type) (a:M A) (F:A-> M B) (G:B-> M C) 
   (f:C->U), star (star a F) G f = star a (fun x:A => star (F x) G) f.
trivial.
Qed.

(** ** Properties of distributions *)
(** *** Expected properties of measures *)
Definition monotonic (A:Type) (m:M A) : Prop := forall f g:A->U, fle f g -> (m f) <= (m g).

Definition stable_eq (A:Type) (m:M A) : Prop :=  forall f g:A->U, feq f g -> (m f) == (m g).

Definition stable_inv (A:Type) (m:M A) : Prop := forall f :A->U, m (finv f) <= Uinv (m f).

Definition continuous (A:Type) (m:M A) := forall fn : nat -> A ->  U, 
      (increase fn) -> m (flub fn) <= lub (fun n => m (fn n)).

Definition fplusok (A:Type) (f g : A -> U) := fle f (finv g).
Hint Unfold fplusok.

Lemma fplusok_sym : forall (A:Type) (f g : A -> U) , fplusok f g -> fplusok g f.
unfold fplusok, finv; auto.
Qed.
Hint Immediate fplusok_sym.

Definition stable_plus (A:Type) (m:M A) : Prop :=
  forall f g:A->U, fplusok f g -> m (fplus f g) == (m f) + (m g).

Definition le_plus (A:Type) (m:M A) : Prop :=
  forall f g:A->U,  fplusok f g -> (m f) + (m g) <= m (fplus f g).

Definition le_esp (A:Type) (m:M A) : Prop :=
  forall f g:A->U,  (m f) & (m g) <= m (fesp f g).

Definition le_plus_cte (A:Type) (m:M A) : Prop :=
  forall (f :A->U) (k:U),  m (fplus f (f_cte A k))  <= m f + k.

Definition stable_mult (A:Type) (m:M A) : Prop :=
  forall (k:U) (f:A -> U), m (fmult k f) == k * (m f).

(** *** Stability for equality *)
Lemma monotonic_stable_eq : forall (A:Type) (m:M A), (monotonic m) -> (stable_eq m).
red; unfold monotonic, fle.
intros; apply Ule_antisym; auto.
Qed.
Hint Resolve monotonic_stable_eq.

Lemma stable_minus_distr : forall (A:Type) (m:M A), 
     stable_plus m -> stable_inv m -> monotonic m -> 
     forall (f g : A -> U), fle g f -> m (fminus f g) == m f - m g.
intros A m splus sinv smon; intros.
assert (m g <= m f); auto.
assert (forall x, fminus f g x <= finv g x).
intros; unfold fminus,Uminus,finv; auto.
setoid_replace (m f) with (m (fminus f g) + m g); auto.
apply Ueq_sym; apply Uplus_minus_simpl_right.
apply Ule_trans with ([1-](m (finv g))); auto.
rewrite <- (splus (fminus f g)  g).
apply (monotonic_stable_eq smon); auto; repeat red; unfold fplus; intros; auto.
repeat red; intros; auto.
Qed.

Hint Resolve stable_minus_distr.

Lemma inv_minus_distr : forall (A:Type) (m:M A), 
     stable_plus m -> stable_inv m -> monotonic m -> 
     forall (f : A -> U), m (finv f) == m (f_one A) - m f.
intros A m splus sinv smon; intros.
apply Ueq_trans with (m (fminus (f_one A) f)); auto.
apply (monotonic_stable_eq smon); repeat red; unfold fminus,finv,f_one; intros; auto.
Qed.
Hint Resolve inv_minus_distr.

Lemma le_minus_distr : forall (A : Type)(m:M A),
    monotonic m ->  forall  (f g:A -> U), m (fminus f g) <= m f.
intros A m smon; intros.
apply smon; repeat red; unfold fminus; auto.
Qed.
Hint Resolve le_minus_distr.

Lemma le_plus_distr : forall (A : Type)(m:M A),
    stable_plus m -> stable_inv m -> monotonic m -> 
    forall (f g:A -> U), m (fplus f g) <= m f + m g.
intros A m splus sinv smon; intros.
apply Ule_trans with (m (fplus (fminus f (fesp f g)) g)).
apply smon; unfold fle,fplus,fminus,fesp; intros; auto. 
rewrite (splus (fminus f (fesp f g)) g).
Usimpl; auto.
repeat red; unfold fminus,fesp,finv; auto.
Qed.
Hint Resolve le_plus_distr.

Lemma le_esp_distr : forall (A : Type) (m:M A), 
     stable_plus m -> stable_inv m -> monotonic m -> le_esp m.
intros A m splus sinv smon; unfold le_esp,fesp,Uesp; intros.
apply Ule_trans with (m (finv (fplus (finv f) (finv g)))); auto.
rewrite inv_minus_distr; auto.
apply Ule_trans with 
  (m (f_one A) -  (m (finv f) + m (finv g))); auto.
apply Ule_trans with (m f - [1-] m g) ; repeat Usimpl; auto.
rewrite inv_minus_distr; auto.
apply Ule_trans with (m f - m (finv g)) ; repeat Usimpl.
apply Uminus_le_compat_right; trivial.
rewrite <- Uminus_assoc_left.
rewrite Uminus_assoc_right; repeat Usimpl; auto.
Qed.


(** *** Monotonicity *)
Lemma unit_monotonic : forall (A:Type) (x:A), monotonic (unit x).
red in |- *; unfold unit, fle in |- *; auto.
Qed.

Lemma star_monotonic : forall (A B:Type) (m:M A) (F:A -> M B),
   monotonic m -> (forall a:A, monotonic (F a)) -> monotonic (star m F).
unfold monotonic, star in |- *; intros.
apply H.
red in |- *; auto.
Qed.


Lemma unit_stable_eq : forall (A:Type) (x:A), stable_eq (unit x).
intros; apply monotonic_stable_eq.
apply unit_monotonic; auto.
Qed.

Lemma star_stable_eq : forall (A B:Type) (m:M A) (F:A -> M B),
   stable_eq m -> (forall a:A, stable_eq (F a)) -> stable_eq (star m F).
unfold stable_eq, star in |- *; auto.
Qed.

(** *** Stability for inversion *)
Lemma unit_stable_inv : forall (A:Type) (x:A), stable_inv (unit x).
red in |- *; intros.
unfold unit in |- *.
auto.
Qed.

Lemma star_stable_inv : forall (A B:Type) (m:M A) (F:A -> M B),
   stable_inv m ->  monotonic m 
   -> (forall a:A, stable_inv (F a)) -> (forall a:A, monotonic (F a))
   -> stable_inv (star m F).
unfold stable_inv in |- *; intros.
unfold star in |- *.
apply Ule_trans with (m (finv (fun x:A => F x f))); trivial.
apply H0.
intros x; apply (H1 x f).
Qed.

(** *** Stability for addition *)
Lemma unit_stable_plus : forall (A:Type) (x:A), stable_plus (unit x).
red in |- *; intros.
unfold unit in |- *.
auto.
Qed.

Lemma star_stable_plus : forall (A B:Type) (m:M A) (F:A -> M B),
   stable_plus m -> stable_eq m -> 
   (forall a:A, forall f g, fplusok f g -> (F a f) <= Uinv (F a g))
   -> (forall a:A, stable_plus (F a)) -> stable_plus (star m F).
unfold stable_plus in |- *; intros.
unfold star in |- *.
apply Ueq_trans with (m (fplus (fun x:A => F x f) (fun x:A => F x g))); trivial.
apply H0.
intros x; apply (H2 x f g H3).
apply H.
repeat red.
unfold finv; intros; auto.
Qed.

Lemma unit_le_plus : forall (A:Type) (x:A), le_plus (unit x).
red in |- *; intros.
unfold unit in |- *.
auto.
Qed.

Lemma star_le_plus : forall (A B:Type) (m:M A) (F:A -> M B),
   le_plus m -> monotonic m -> 
   (forall a:A, forall f g, fplusok f g -> (F a f) <= Uinv (F a g))
   -> (forall a:A, le_plus (F a)) -> le_plus  (star m F).
unfold le_plus in |- *; intros.
unfold star in |- *.
apply Ule_trans with (m (fplus (fun x:A => F x f) (fun x:A => F x g))); trivial.
apply H.
repeat red.
unfold finv; intros; auto.
apply H0.
repeat red; intros.
unfold fplus at 1; auto.
Qed.

(** *** Stability for product *)
Lemma unit_stable_mult : forall (A:Type) (x:A), stable_mult (unit x).
red in |- *; intros.
unfold unit in |- *; auto.
Qed.

Lemma star_stable_mult : forall (A B:Type) (m:M A) (F:A -> M B),
   stable_mult m -> stable_eq m -> (forall a:A, stable_mult (F a)) -> stable_mult (star m F).
unfold stable_mult in |- *; intros.
unfold star in |- *.
apply Ueq_trans with (m (fmult k (fun x:A => F x f))); trivial.
apply H0.
intro.
unfold fmult at 2 in |- *; trivial.
Qed.

(** *** Continuity *)
Lemma unit_continuous : forall (A:Type) (x:A), continuous (unit x). 
red; unfold unit; intros; auto.
Qed.

Lemma star_continuous : forall (A B : Type) (m : M A)(F: A -> M B), 
    monotonic m-> continuous m -> 
   (forall x, continuous (F x)) -> (forall x, monotonic (F x)) -> continuous (star m F).
red; unfold star; intros.
apply Ule_trans with (m (fun x => lub (fun n => (F x (fn n))))).
apply H; red; intros.
apply (H1 x); auto.
apply H0 with (fn := fun n x => F x (fn n)); intros; auto.
repeat red; intros.
apply (H2 x); auto.
Qed.


End Monad.

