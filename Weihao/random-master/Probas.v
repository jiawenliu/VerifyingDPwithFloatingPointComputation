(** * Probas.v: The monad for distributions *)

Require Export Uprop.
Require Export Monads.
Require Arith.
Set Implicit Arguments.
Module Proba (Univ:Universe).
Module MP := (Monad Univ).
(* begin hide *)
Import Univ.
Import MP.
Import MP.UP.
(* end hide *)
(** ** Definition of distribution
Distributions are measure functions such that
    - $\mu (1-f) \leq 1-\mu(f)$
    - $f \leq 1 -g \Ra \mu(f+g)=\mu(f)+\mu(g)$
    - $\mu(k\times f) = k \times \mu(f)$
    - $f\leq g \Ra \mu(f)\leq\mu(g)$
*)
Record distr (A:Type) : Type := 
  {mu : M A;
   mu_stable_inv : stable_inv mu; 
   mu_stable_plus : stable_plus mu;
   mu_stable_mult : stable_mult mu;
   mu_monotonic : monotonic mu}.

Hint Resolve mu_stable_plus mu_stable_inv mu_stable_mult mu_monotonic.

(** ** Properties of measures *)
Lemma mu_stable_eq : forall (A : Type)(m: distr A), stable_eq (mu m).
intros; apply monotonic_stable_eq; auto.
Qed.
Hint Resolve mu_stable_eq.
Implicit Arguments mu_stable_eq [A].

Lemma mu_zero : forall (A : Type)(m: distr A), mu m (f_zero A) == 0.
intros.
apply Ueq_trans with (mu m (fmult 0 (f_zero A))); auto.
apply mu_stable_eq; unfold fmult; auto.
apply Ueq_trans with (0 * (mu m (f_zero A))); auto.
apply mu_stable_mult; auto.
Qed.
Hint Resolve mu_zero.

Lemma mu_one_inv : forall (A : Type)(m:distr A),
   mu m (f_one A) == 1 -> forall f, mu m (finv f) == [1-] (mu m f).
intros; apply Ule_antisym.
apply (mu_stable_inv m f).
apply Uplus_le_simpl_left with (mu m f); auto.
setoid_rewrite (Uinv_opp_right (mu m f)).
apply Ule_trans with (mu m (fun x => (f x) + [1-] (f x))).
setoid_rewrite <- H; apply (mu_monotonic m); auto.
assert (H1 : fplusok f (finv f)).
repeat red; unfold finv; auto.
setoid_rewrite <- (mu_stable_plus m H1); auto.
Qed.
Hint Resolve mu_one_inv.

Lemma mu_le_minus : forall (A : Type)(m:distr A) (f g:A -> U),
     mu m (fminus f g) <= mu m f.
intros; apply mu_monotonic; repeat red; unfold fminus; auto.
Qed.
Hint Resolve mu_le_minus.

Lemma mu_le_plus : forall (A : Type)(m:distr A) (f g:A -> U),
     mu m (fplus f g) <= mu m f + mu m g.
intros; apply Ule_trans with (mu m (fplus (fminus f (fesp f g)) g)).
apply mu_monotonic.
unfold fle,fplus,fminus,fesp; intros; auto. 
rewrite (mu_stable_plus m (f:=fminus f (fesp f g)) (g:=g)).
Usimpl; auto.
repeat red; unfold fminus,fesp,finv; auto.
Qed.
Hint Resolve mu_le_plus.

Lemma mu_cte : forall (A : Type)(m:(distr A)) (c:U),
   mu m (f_cte A c) == c * mu m (f_one A).
intros.
apply Ueq_trans with (mu m (fun x => c * 1)).
apply (mu_stable_eq m); auto.
unfold f_one; setoid_rewrite <- (mu_stable_mult m c (fun x => 1)); auto.
Qed.
Hint Resolve mu_cte.

Lemma mu_cte_le :   forall (A : Type)(m:(distr A)) (c:U),
   mu m (f_cte A c) <= c.
intros; apply Ule_trans with (c * mu m (f_one A)); auto.
Qed.


Lemma mu_cte_eq : forall (A : Type)(m:(distr A)) (c:U),
   mu m (f_one A) == 1 -> mu m (f_cte A c) == c.
intros; apply Ueq_trans with (c * mu m (f_one A)); auto.
setoid_rewrite H; auto.
Qed.

Hint Resolve mu_cte_le mu_cte_eq.

Lemma mu_stable_mult_right : forall (A : Type)(m:(distr A)) (c:U) (f : A -> U),
   mu m (fun x => (f x) * c) == (mu m f) * c.
intros; apply Ueq_trans with 
   (mu m (fun x => c * (f x))).
apply mu_stable_eq; auto.
apply Ueq_trans with (c * mu m f); auto.
exact (mu_stable_mult m c f).
Qed.

Lemma mu_stable_minus : forall (A:Type) (m:distr A)(f g : A -> U),
 fle g f -> mu m (fun x => f x - g x) == mu m f - mu m g.
intros.
assert (mu m g <= mu m f).
apply (mu_monotonic m); auto.
assert (forall x, f x - g x <= [1-](g x)).
intros; unfold Uminus; auto.
setoid_replace (mu m f) with (mu m (fun x : A => f x - g x) + mu m g); auto.
apply Ueq_sym; apply Uplus_minus_simpl_right.
apply Ule_trans with ([1-](mu m (fun x => [1-] g x))); auto.
apply Uinv_le_perm_right.
apply (mu_stable_inv m g); auto.
apply Uinv_le_compat.
apply (mu_monotonic m); red; intros; auto.
rewrite <- (mu_stable_plus m (f:=fun x : A => f x - g x)  (g:=g)).
apply (mu_stable_eq m); repeat red; unfold fplus; intros; auto.
repeat red; intros; unfold finv; auto.
Qed.

Lemma mu_inv_minus : 
forall (A:Type) (m:distr A)(f: A -> U), mu m (finv f) == mu m (f_one A) - mu m f.
intros; apply Ueq_trans with (mu m (fun x => f_one A x - f x)).
apply (mu_stable_eq m); repeat red; unfold finv,f_one; intros; auto.
apply mu_stable_minus; auto.
Qed.

Lemma mu_inv_minus_inv : forall (A:Type) (m:distr A)(f: A -> U), 
     mu m (finv f) + [1-](mu m (f_one A)) == [1-](mu m f).
intros; apply Uminus_eq_perm_right.
apply Uinv_le_compat.
apply (mu_monotonic m); unfold f_one; auto.
unfold Uminus; Usimpl.
rewrite mu_inv_minus; repeat Usimpl.
unfold Uminus.
apply Uinv_eq_compat; auto.
Qed.

Lemma mu_le_esp_inv : forall (A:Type) (m:distr A)(f g : A -> U),
 ([1-]mu m (finv f)) & mu m g <= mu m (fesp f g).
intros; rewrite Uesp_sym.
apply Uplus_inv_le_esp; Usimpl.
apply Ule_trans with (mu m (fplus (fesp f g) (finv f))); auto.
apply (mu_monotonic m); unfold fplus, fle, fesp,finv; intros; auto.
rewrite Uesp_sym; auto.
Qed.
Hint Resolve mu_le_esp_inv.

Lemma mu_stable_inv_inv : forall (A:Type) (m:distr A)(f : A -> U),
             mu m f <= [1-] mu m (finv f).
intros; apply Ule_trans with (mu m (finv (finv f))).
apply (mu_monotonic m); auto.
apply (mu_stable_inv m); auto.
Qed.
Hint Resolve  mu_stable_inv_inv.

Lemma mu_le_esp : forall (A:Type) (m:distr A)(f g : A -> U),
 mu m f & mu m g <= mu m (fesp f g).
intros; apply Ule_trans with (([1-]mu m (finv f)) & mu m g); auto.
Qed.
Hint Resolve mu_le_esp.


(** ** Monadic operators for distributions *)
Definition Munit : forall A:Type, A -> distr A.
intros A x.
exists (unit x).
apply unit_stable_inv.
apply unit_stable_plus.
apply unit_stable_mult.
apply unit_monotonic.
Defined.

Definition Mlet : forall A B:Type, (distr A) -> (A -> distr B) -> distr B.
intros A B mA mB.
exists (star (mu mA) (fun x => (mu (mB x)))).
apply star_stable_inv; auto.
apply star_stable_plus; auto.
intros;apply Ule_trans with ([1-] (mu (mB a) g)); auto.
apply Ule_trans with (mu (mB a) (fun a => ([1-] (g a)))); auto.
apply (mu_monotonic (mB a)); auto.
apply (mu_stable_inv (mB a)) with (f:=g).
apply star_stable_mult; auto.
apply star_monotonic; auto.
Defined.

(** ** Operations on distributions *)

Definition le_distr (A:Type) (m1 m2:distr A) := forall f, mu m1 f <= mu m2 f.

Definition eq_distr (A:Type) (m1 m2:distr A) := forall f, mu m1 f == mu m2 f.

Lemma le_distr_antisym : forall (A:Type) (m1 m2:distr A),
  le_distr m1 m2 -> le_distr m2 m1 -> eq_distr m1 m2.
red; intros; apply Ule_antisym; auto.
Qed.

Lemma le_distr_refl : forall (A:Type) (m :distr A), le_distr m m.
unfold le_distr; auto.
Qed.

Lemma eq_distr_sym : forall A (m1 m2:distr A), eq_distr m1 m2 -> eq_distr m2 m1.
unfold eq_distr; auto.
Qed.

Lemma eq_distr_refl : forall A (m:distr A), eq_distr m m.
unfold eq_distr; auto.
Qed.

Lemma eq_distr_trans : forall A (m1 m2 m3:distr A), 
      eq_distr m1 m2 -> eq_distr m2 m3->eq_distr m1 m3.
unfold eq_distr; intros.
apply Ueq_trans with (mu m2 f); auto.
Qed.

Hint Resolve eq_distr_refl.
Hint Immediate eq_distr_sym.

Lemma distr_setoid : forall (A:Type), Setoid_Theory  (distr A) (eq_distr (A:=A)).
intros; constructor; red ; auto.
exact (eq_distr_trans (A:=A)).
Qed.

Lemma le_distr_trans : forall (A:Type) (m1 m2 m3:distr A),
  le_distr m1 m2 -> le_distr m2 m3 -> le_distr m1 m3.
unfold le_distr; intros.
apply Ule_trans with (mu m2 f); auto.
Qed.

Hint Resolve le_distr_refl.
Hint Unfold le_distr.

Add Parametric Setoid A : (@distr A) (@eq_distr A) (@distr_setoid A) as Distr_Setoid. 

Lemma Munit_compat : forall A (x y : A), x=y -> eq_distr (Munit x) (Munit y).
intros; subst; auto.
Qed.

Lemma Mlet_compat : forall (A B : Type) (m1 m2:distr A) (M1 M2 : A-> distr B), 
  eq_distr m1 m2 -> (forall x, eq_distr (M1 x) (M2 x)) -> 
  eq_distr (Mlet m1 M1) (Mlet m2 M2).
unfold eq_distr,Mlet,star; simpl; intros.
apply Ueq_trans with (mu m2 (fun x : A => mu (M1 x) f)); auto.
apply mu_stable_eq; red; auto.
Qed.

Lemma Munit_eq : forall (A:Type) (q:A->U) x, mu (Munit x) q == q x.
trivial.
Qed.

Lemma le_distr_gen : forall (A:Type) (m1 m2:distr A),
  le_distr m1 m2 -> forall f g,  fle f g -> mu m1 f <= mu m2 g.
intros; apply Ule_trans with (mu m2 f); auto.
apply (mu_monotonic m2); auto.
Qed.

(** ** Properties of monadic operators *)
Lemma Mlet_unit : forall (A B:Type) (x:A) (m:A -> distr B), eq_distr (Mlet (Munit x) m) (m x).
red; intros; simpl; rewrite law1; trivial.
Qed.

Lemma M_ext : forall (A:Type) (m:distr A), eq_distr (Mlet m (fun x => (Munit x))) m.
red; intros; simpl;rewrite law2; trivial.
Qed.

Lemma Mcomp : forall (A B C:Type) (m1:(distr A)) (m2:A -> distr B) (m3:B -> distr C),
     eq_distr (Mlet (Mlet m1 m2) m3) (Mlet m1 (fun x:A => (Mlet (m2 x) m3))).
red; intros; simpl.
rewrite law3; trivial.
Qed.

Lemma Mlet_mon : forall (A B:Type) (m1 m2: distr A) (f1 f2 : A -> distr B),
  le_distr m1 m2 -> (forall x, le_distr (f1 x) (f2 x)) -> le_distr (Mlet m1 f1) (Mlet m2 f2).
red; intros; simpl.
unfold star; auto.
apply (le_distr_gen H).
red; red in H0; auto.
Qed.

(** ** A specific distribution *)
Definition distr_null : forall A : Type, distr A.
intro A; exists (fun (f : A -> U) => 0); try red; auto.
Defined.

Lemma le_distr_null : forall (A:Type) (m : distr A), le_distr (distr_null A) m.
red; intros.
unfold distr_null; simpl; auto.
Qed.
Hint Resolve le_distr_null.

(** ** Least upper bound of increasing sequences of distributions *)
Section Lubs.
Variable A : Type.
Variable muf : nat -> (distr A).
Hypothesis muf_mon : forall n m:nat, (n <= m)%nat -> le_distr (muf n) (muf m).

Definition mu_lub_ : M A := fun f => lub (fun n => mu (muf n) f).

Definition mu_lub: distr A.
exists mu_lub_; try red; unfold mu_lub_; intros.

red in muf_mon; apply lub_inv; repeat red; intros; auto.

unfold fplus;apply Ueq_trans with 
(lub (fun n:nat => (mu (muf n) f) + (mu (muf n) g))); auto.
apply lub_eq_stable; auto.
intro; exact (mu_stable_plus (muf n) H); auto.
apply (@lub_eq_plus (fun n:nat => mu (muf n) f) 
                   (fun n:nat => mu (muf n) g));
intros; apply muf_mon; auto.
unfold fmult;
apply Ueq_trans with 
(lub (fun n:nat => k * (mu (muf n) f))).
apply lub_eq_stable; auto.
intro; exact (mu_stable_mult (muf n) k f); auto.
exact (lub_eq_mult k (fun n:nat => mu (muf n) f)).
apply lub_le_stable; auto.
intros; apply (mu_monotonic (muf n)); auto.
Defined.

Lemma mu_lub_le : forall n:nat, le_distr (muf n) mu_lub.
red; intros; simpl; unfold mu_lub_; auto.
change (((fun n0:nat => mu (muf n0) f) n)
       <= lub (fun n0:nat => mu (muf n0) f)).
apply le_lub.
Qed.

Lemma mu_lub_sup : forall m:(distr A), (forall n:nat, le_distr (muf n) m) -> le_distr mu_lub m.
red; intros; simpl; unfold mu_lub_; auto.
apply lub_le.
red in H; auto.
Qed.

End Lubs.

(** ** Distribution for [flip]
The distribution associated to [flip ()] is 
       $f \mapsto \frac{1}{2}f(true)+\frac{1}{2}f(false)$ *)
Definition flip : (M bool) := fun (f : bool -> U) => [1/2] * (f true) + [1/2] * (f false).

Lemma flip_stable_inv : stable_inv flip.
unfold flip, stable_inv, finv; intros; auto.
Qed.

Lemma flip_stable_plus : stable_plus flip.
unfold flip, stable_plus, fplus; intros; auto.
setoid_rewrite (Udistr_plus_left [1/2] (H true)).
setoid_rewrite (Udistr_plus_left [1/2] (H false)).
repeat norm_assoc_right.
apply Uplus_eq_compat_right.
repeat norm_assoc_left; apply Uplus_eq_compat_left; auto.
Qed.

Lemma flip_stable_mult : stable_mult flip.
unfold flip, stable_mult, fmult; intros; auto.
setoid_replace ([1/2]* (k * f true)) with (k * ([1/2]* f true)); auto.
setoid_replace ([1/2]* (k * f false))   with (k * ([1/2]* f false)); auto.
assert (([1/2]* f true) <= ([1-] ([1/2]* f false))); auto.
setoid_rewrite (Udistr_plus_left k H); auto.
Qed.

Lemma flip_monotonic : monotonic flip.
unfold monotonic, flip; intros.
red in H.
apply Ule_trans with ([1/2]* g true +[1/2]* f false ); auto.
Qed.

Definition ctrue (b:bool) := if b then 1 else 0.
Definition cfalse (b:bool) := if b then 0 else 1.

Lemma flip_ctrue : flip ctrue == [1/2].
unfold flip, ctrue; simpl; auto.
setoid_rewrite (Umult_one_right [1/2]).
setoid_rewrite (Umult_zero_right [1/2]); auto.
Qed.

Lemma flip_cfalse : flip cfalse == [1/2].
unfold flip, cfalse; simpl; auto.
setoid_rewrite (Umult_one_right [1/2]).
setoid_rewrite (Umult_zero_right [1/2]); auto.
Qed.

Hint Resolve flip_ctrue flip_cfalse.

Definition Flip  : distr bool.
exists flip.
apply flip_stable_inv.
apply flip_stable_plus.
apply flip_stable_mult.
apply flip_monotonic.
Defined.

(** ** Uniform distribution beween 0 and n *)

(** *** Definition of [fnth]
        [fnth n k] is defined as $\frac{1}{n+1}$ *)

Definition fnth (n:nat) : nat -> U := fun k => ([1/]1+n).           

(** *** Basic properties of [fnth] *)


Lemma Unth_eq : forall n, Unth n == [1-] (sigma (fnth n) n).
intro; exact (Unth_prop n).
Qed.
Hint Resolve Unth_eq.

Lemma sigma_fnth_one : forall n, sigma (fnth n) (S n) == 1.
intros; rewrite sigma_S.
unfold fnth at 1.
rewrite (Unth_eq n); auto.
Qed.
Hint Resolve sigma_fnth_one.

Lemma Unth_inv_eq : forall n, [1-] ([1/]1+n) == sigma (fnth n) n.
intro; setoid_rewrite (Unth_eq n); auto.
Qed.

Lemma sigma_fnth_sup : forall n m, (m > n) -> sigma (fnth n) m == sigma (fnth n) (S n).
intros.
assert ((S n) <= m)%nat; auto with arith.
elim H0; intros; auto.
rewrite sigma_S; auto.
setoid_rewrite H2.
assert (m0 > n); auto with arith.
setoid_rewrite (sigma_fnth_one n); auto.
Qed.


Lemma sigma_fnth_le : forall n m, (sigma (fnth n) m) <= (sigma (fnth n) (S n)).
intros; setoid_rewrite (sigma_fnth_one n); auto.
Qed.

Hint Resolve sigma_fnth_le.

(** [fnth] is a retract *)
Lemma fnth_retract : forall n:nat,(retract (fnth n) (S n)).
red; intros.
unfold fnth at 1.
apply Ule_trans with ([1-] (sigma (fnth n) n)); auto with arith.
Qed.

Implicit Arguments fnth_retract [].

(** *** Distribution for [random n]
The distribution associated to [random n] is 
       $f \mapsto \Sigma_{i=0}^n \frac{f(i)}{n+1}$
       we cannot factorize $\frac{1}{n+1}$ because of possible overflow *)

Definition random (n:nat):M nat:= fun (f:nat->U) => sigma (fun k => Unth n *  f k) (S n).


(** *** Properties of [random] *)

Lemma random_stable_inv : forall n, stable_inv (random n).
unfold random, stable_inv, finv; intros; auto.
setoid_rewrite (sigma_inv f (fnth_retract n)); auto.
Qed.

Lemma random_stable_plus : forall n, stable_plus (random n).
unfold random, stable_plus, fplus; intros; auto.
unfold fplusok, fle, finv in H.
apply Ueq_trans with 
 (sigma (fun k : nat => ([1/]1+n * f k) + ([1/]1+n  * g k)) (S n)).
apply sigma_eq_compat; intros.
assert (f k <= [1-] (g k)); auto.
apply sigma_plus with (f:=fun k : nat => Unth n * f k)
                      (g:=fun k : nat => Unth n * g k); auto.
Qed.

Lemma random_stable_mult : forall n, stable_mult (random n).
unfold random, stable_mult, fmult; intros; auto.
apply Ueq_trans with 
 (sigma (fun l : nat => k * ([1/]1+n * f l)) (S n)).
apply sigma_eq_compat; intros; auto.
apply sigma_mult with (f:=fun k : nat => Unth n * f k).
red; intros.
apply Ule_trans with ([1/]1+n); auto.
apply Ule_trans with ([1-] (sigma (fun k1 => Unth n) k0)); auto.
apply (fnth_retract n k0); auto.
Qed.

Lemma random_monotonic : forall n, monotonic (random n).
unfold monotonic, random; intros.
red in H.
apply sigma_le_compat; auto.
Qed.

Definition Random (n:nat) : (distr nat).
exists (random n).
apply random_stable_inv.
apply random_stable_plus.
apply random_stable_mult.
apply random_monotonic.
Defined.

Lemma random_total : forall n : nat,  mu (Random n) (f_one nat) == 1.
intros; simpl; unfold random.
unfold f_one.
apply Ueq_trans with  (sigma (fnth n) (S n)).
apply sigma_eq_compat.
intros; repeat Usimpl; auto.
auto.
Qed.

(** * Nondeterministic choice *)

Record Ndistr (A:Type): Type := 
   {nu : M A; nu_monotonic : monotonic nu; nu_continuous : continuous nu; nu_le_esp: le_esp nu}.

Hint Resolve nu_monotonic nu_continuous nu_le_esp.

Definition Nunit (A:Type) (x:A) : Ndistr A.
exists (unit x).
apply unit_monotonic.
apply unit_continuous.
red; auto.
Defined.

Definition Nlet (A B:Type)(n:Ndistr A) (N:A->Ndistr B): Ndistr B.
exists (star (nu n) (fun x => nu (N x))); auto.
apply star_monotonic; auto.
apply star_continuous; auto.
red; unfold star; intros.
apply Ule_trans with (nu n (fun x : A => nu (N x) f & nu (N x) g)).
apply (nu_le_esp n) with (f:=fun x : A => nu (N x) f) (g:=fun x : A => nu (N x) g).
apply (nu_monotonic n); red; intros.
apply (nu_le_esp (N x) f g).
Defined.

 
Definition Nif (A:Type) (nb: Ndistr bool) (n1 n2 :Ndistr A): Ndistr A := 
     Nlet nb (fun b => if b then n1 else n2).

Definition Ndistr_cte : forall A, forall x:U, Ndistr A.
intros;  exists (fun (f:A->U) => x).
red; auto.
red; simpl; intros.
apply le_lub with (f:= fun (n:nat) => x) (n:=O); auto.
red; auto.
Defined.

Definition Nmin : forall A, Ndistr A -> Ndistr A -> Ndistr A. 
intros A n1 n2; exists (fun f => min (nu n1 f) (nu n2 f)).
red; destruct n1; destruct n2; simpl; intros.
apply min_le_compat; auto.
red; intros.
apply Ule_trans with 
  (min (lub (fun n => nu n1 (fn n))) (lub (fun n => nu n2 (fn n)))); auto.
apply min_le_compat; auto.
apply (nu_continuous n1); auto.
apply (nu_continuous n2); auto.
apply min_lub_le_incr with (f:=fun n => nu n1 (fn n)) 
           (g:=fun n => nu n2 (fn n)).
red; intros; apply (nu_monotonic n1); auto.
red; intros; apply (nu_monotonic n2); auto.
red; intros.
apply Ule_trans with (min (nu n1 f & nu n1 g) (nu n2 f & nu n2 g)).
apply Uesp_min.
apply min_le_compat.
apply (nu_le_esp n1).
apply (nu_le_esp n2).
Defined.

Lemma Ndistr_eq_esp : forall (A:Type) (n:Ndistr A) f g, 1 <= nu n f -> nu n g == nu n (fesp f g).
intros; apply Ule_antisym.
apply Ule_trans with (nu n f & nu n g).
apply Ule_trans with (1 & nu n g); auto.
apply (nu_le_esp n); auto.
apply (nu_monotonic n); unfold fesp; red; auto.
Qed.
Hint Resolve Ndistr_eq_esp.

Definition le_ndistr (A:Type)(m1 m2 : Ndistr A) := forall f,  nu m1 f <= nu m2 f.

End Proba.
