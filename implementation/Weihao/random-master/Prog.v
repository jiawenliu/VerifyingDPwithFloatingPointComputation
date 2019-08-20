(** * Prog.v: Composition of distributions *)

Require Export Probas.
Set Implicit Arguments.

Module Rules (Univ:Universe).
Module PP := (Proba Univ).
(* begin hide *)
Import Univ.
Import PP.
Import PP.MP.
Import PP.MP.UP.
(* end hide *)

(** ** Conditional *)
Definition Mif (A:Type) (b:distr bool) (m1 m2: distr A) 
    := Mlet b (fun x:bool => if x then m1 else m2).

Lemma Mif_mon : forall (A:Type) (b b':distr bool) (m1 m2 m1' m2': distr A),
    le_distr b b' -> le_distr m1 m1' -> le_distr m2 m2'
    -> le_distr (Mif b m1 m2) (Mif b' m1' m2').
intros; unfold Mif; apply Mlet_mon; auto.
destruct x; auto.
Qed. 

(** ** Fixpoints *)
Section Fixpoints.
(** *** Hypotheses *)
Variables A B : Type.

Variable F : (A -> distr B) -> A -> distr B.

Hypothesis F_mon : forall f g : A -> distr B, 
  (forall x, le_distr (f x) (g x)) -> forall x, le_distr (F f x) (F g x).

(** *** Iteration of the functional $F$ from the $0$-distribution *)
Fixpoint iter (n:nat) : A -> (distr B)
:= match n with | O => fun x => (distr_null B)
                | S n => fun x => F (iter n) x
   end.

Definition Flift (dn:A->nat->distr B)(x:A)(n:nat):(distr B)
      := F (fun y => dn y n) x.

Lemma Flift_mon : forall dn : A -> nat -> distr B,
(forall (x:A) (n m:nat), (n <= m)%nat ->le_distr (dn x n) (dn x m))
 -> forall (x:A) (n m:nat), (n <= m)%nat ->le_distr (Flift dn x n) (Flift dn x m).
unfold Flift; red; intros.
apply F_mon; auto.
Qed.

Hypothesis F_continuous : forall (dn:A->nat->distr B)
  (dnmon : forall x n m,(n <= m)%nat ->le_distr (dn x n) (dn x m))
  (x:A),
  (le_distr (F (fun y => mu_lub (dn y) (dnmon y)) x) 
               (mu_lub (Flift dn x) (Flift_mon dn dnmon x))).

Let muf (x:A) (n:nat) := (iter n x).

Lemma muf_mon_succ :  forall (n:nat) (x:A), le_distr (muf x n) (muf x (S n)).
induction n; unfold muf, le_distr; simpl; intros.
auto.
apply F_mon; auto.
Qed.

Lemma muf_mon :  forall (x:A) (n m:nat), (n <= m)%nat -> le_distr (muf x n) (muf x m).
induction 1; auto.
apply le_distr_trans with (muf x m); auto.
apply muf_mon_succ.
Qed.

(** *** Definition *)
Definition Mfix (x:A) := mu_lub (fun n => iter n x) (muf_mon x).
(** *** Properties *)
Lemma Mfix_le_iter :  forall (x : A) (n:nat), le_distr (iter n x) (Mfix x).
red; intros; unfold Mfix.
apply mu_lub_le with (muf:=fun n0:nat => iter n0 x); trivial.
Qed.
Hint Resolve Mfix_le_iter.

Lemma Mfix_iter_le :  forall  (m:A->distr B), 
              (forall (x : A) (n:nat), le_distr (iter n x) (m x)) -> forall x, le_distr (Mfix x) (m x).
red; intros; unfold Mfix.
apply mu_lub_sup with (muf:=fun n0:nat => iter n0 x); trivial.
Qed.
Hint Resolve Mfix_iter_le.

Lemma Mfix_le : forall x : A, le_distr (Mfix x) (F Mfix x).
unfold Mfix at 1; red; intros.
apply mu_lub_sup; trivial.
destruct n; simpl; auto.
Qed.

Lemma Mfix_sup : forall x : A, le_distr (F Mfix x) (Mfix x).
unfold Mfix.
intro x.
pose (dn:=fun (x0:A) (n:nat) => iter n x0).
apply le_distr_trans with 
  (mu_lub (Flift dn x) (Flift_mon dn muf_mon x)).
apply F_continuous with 
 (dn:=fun (x0:A) (n:nat) => iter n x0) (dnmon:=muf_mon) (x:=x).
red; auto.
unfold Flift, dn.
intros; apply mu_lub_sup; intros.
apply le_distr_trans with (iter (S n) x); auto.
apply mu_lub_le with (muf:=fun n0:nat => iter n0 x); auto.
Qed.

Lemma Mfix_eq : forall x : A, eq_distr (Mfix x) (F Mfix x).
red; intros; apply Ule_antisym.
apply Mfix_le; trivial.
apply Mfix_sup; trivial.
Qed.

End Fixpoints.

Lemma Mfix_le_stable : forall (A B:Type) F G
        (Fmon:forall f g : A -> distr B, (forall x : A, le_distr (f x) (g x)) ->
                                                        forall x : A, le_distr (F f x) (F g x))
        (Gmon:forall f g : A -> distr B, (forall x : A, le_distr (f x) (g x)) ->
                                                        forall x : A, le_distr (G f x) (G g x)),
        (forall f x, le_distr (F f x) (G f x)) -> forall x, le_distr (Mfix F Fmon x) (Mfix G Gmon x). 
intros.
apply Mfix_iter_le with (m:=Mfix G Gmon); intros.
apply le_distr_trans with (iter G n x0).
generalize x0; clear x0; induction n; simpl; intros; auto.
apply le_distr_trans with (G (iter F n) x0); auto.
apply Mfix_le_iter.
Qed.

(** ** Continuity *)

Section Continuity.

Variables A B:Type.
Variable mun : nat -> distr A.
Hypothesis mun_incr : forall n m, ((n <= m)%nat) -> le_distr (mun n) (mun m).
Hypothesis mun_cont : forall n, continuous (mu (mun n)).
Variable Mn : A -> nat -> distr B.
Hypothesis Mn_incr : forall x n m, ((n <= m)%nat) -> le_distr (Mn x n) (Mn x m).
Lemma Mlet_incr : 
             forall n m,(n <= m)%nat ->
             le_distr (Mlet (mun n) (fun x => Mn x n)) (Mlet (mun m) (fun x => Mn x m)). 
intros; apply Mlet_mon; auto.
Qed.

Lemma Mlet_continuous : 
             le_distr (Mlet (mu_lub mun mun_incr) (fun x => mu_lub (Mn x) (Mn_incr x)))
                          (mu_lub (fun n => Mlet (mun n) (fun x => Mn x n)) Mlet_incr).
red; simpl; unfold mu_lub_, star; intro.
apply Ule_trans with 
 (lub (fun n : nat => lub (fun n0 => mu (mun n) (fun x => mu (Mn x n0) f)))).
apply lub_le_stable; intro.
apply (mun_cont n (fn:=fun n0 x  => mu (Mn x n0) f)).
repeat red; intros.
apply Mn_incr; auto with arith.
rewrite (double_lub_simpl 
            (fun n m => mu (mun n) (fun x : A => mu (Mn x m) f))); auto.
intros; apply (@mun_incr n (S n)) with (f:=fun x : A => mu (Mn x m) f); auto with arith.
intros; apply mu_monotonic; repeat red; intros; auto.
apply (@Mn_incr x m (S m)) with (f:=f); auto with arith.
Qed.


Variable Fn : nat -> (A -> distr B) -> A -> distr B.

Hypothesis Fn_mon : forall n (f g : A -> distr B), 
  (forall x, le_distr (f x) (g x)) -> forall x, le_distr (Fn n f x) (Fn n g x).

Hypothesis Fn_incr : forall f x n m, (n <= m)%nat ->le_distr (Fn n f x) (Fn m f x).

Hypothesis Fn_continuous :  forall n (dn:A->nat->distr B)
  (dnmon : forall x n m,(n <= m)%nat -> le_distr (dn x n) (dn x m))
  (x:A),
  (le_distr (Fn n (fun y => mu_lub (dn y) (dnmon y)) x) 
               (mu_lub (Flift (Fn n) dn x) (Flift_mon (Fn n) (Fn_mon n) dn dnmon x))).

Lemma Mfix_incr : forall x, 
             forall n m,(n <= m)%nat ->
             le_distr (Mfix (Fn n) (Fn_mon n) x) (Mfix (Fn m) (Fn_mon m) x).
intros; apply Mfix_le_stable; auto.
Qed.

Lemma mu_lub_mon : 
             forall (f g : A -> distr B), (forall x, le_distr (f x) (g x)) 
             -> forall x, le_distr (mu_lub (fun n => Fn n f x) (Fn_incr f x)) 
                                           (mu_lub (fun n => Fn n g x) (Fn_incr g x)).
repeat red; intros.
simpl; unfold mu_lub_.
apply lub_le_stable;intros.
apply (Fn_mon n f g) with (x:=x); auto.
Qed.

Lemma iter_incr : forall k x, 
             forall n m,(n <= m)%nat ->
             le_distr (iter (Fn n) k x) (iter (Fn m) k x).
induction k; intros; simpl; auto.
apply le_distr_trans with (Fn m (iter (Fn n) k) x); auto.
Qed.
Hint Resolve iter_incr.

Lemma iter_continuous : 
       forall k x, le_distr (iter (fun f x => mu_lub (fun n => Fn n f x) (Fn_incr f x)) k x)
                                   (mu_lub (fun n => iter (Fn n) k x) (iter_incr k x)).
induction k; simpl; intros; auto.
red; simpl; unfold mu_lub_; intros.
apply Ule_trans with 
 (lub (fun n => mu (Fn n (fun x => mu_lub (fun n : nat => iter (Fn n) k x) (iter_incr k x)) x) f)).
apply lub_le_stable; intros.
apply (Fn_mon n); auto with arith.
pose (dn:=fun (x0:A) (n0:nat) =>  iter (Fn n0) k x0).
pose (dnmon:= iter_incr k).
apply Ule_trans with
 (lub  (fun n : nat =>
         mu (mu_lub (Flift (Fn n) dn x)
                            (Flift_mon (Fn n) (Fn_mon n) dn dnmon x)) f)).
apply lub_le_stable; intro.
apply (Fn_continuous n dn dnmon x f).
unfold dn; simpl; unfold mu_lub_,Flift.
rewrite (double_lub_simpl (fun n m => mu (Fn n (fun y : A => iter (Fn m) k y) x) f)); auto.
intros; apply (@Fn_incr (fun y : A => iter (Fn m) k y) x n (S n)); auto with arith.
intros; apply (@Fn_mon n (fun y : A => iter (Fn m) k y) (fun y : A => iter (Fn (S m)) k y)); auto.
Qed.
Hint Resolve iter_continuous.

Lemma MFix_continuous : 
       forall x, 
       le_distr (Mfix (fun f x => mu_lub (fun n => Fn n f x) (Fn_incr f x)) mu_lub_mon x)
                   (mu_lub (fun n => Mfix (Fn n) (Fn_mon n) x) (Mfix_incr x)).
red; intros.
simpl; unfold mu_lub_.
apply Ule_trans with 
 (lub (fun n : nat =>
            mu (mu_lub (fun m => iter (Fn m) n x) (iter_incr n x)) f)).
apply lub_le_stable; intros; apply iter_continuous.
simpl; unfold mu_lub_; auto.
Qed.

End Continuity.

(** * Prog.v: Axiomatic semantics *)
(** ** Definition of correctness judgements
 $\ok{p}{e}{q}$ is defined as $p \leq \mu(e)(q)$ 
 $\up{p}{e}{q}$ is defined as $ \mu(e)(q) \leq p$ *)

Definition ok (A:Type) (p:U) (e:distr A) (q:A->U) := p <= mu e q.

Definition okfun (A B:Type)(p:A->U)(e:A->distr B)(q:A->B->U) 
  := forall x:A, ok (p x) (e x) (q x).

Definition okup (A:Type) (p:U) (e:distr A) (q:A->U) := mu e q <= p.

Definition upfun (A B:Type)(p:A->U)(e:A->distr B)(q:A->B->U) 
  := forall x:A, okup (p x) (e x) (q x).

(** ** Stability properties *)
Lemma ok_le_compat : forall (A:Type) (p p':U) (e:distr A) (q q':A->U),
    p' <= p -> fle q q' -> ok p e q -> ok p' e q'.
unfold ok; intros.
apply Ule_trans with p; auto.
apply Ule_trans with (mu e q); auto.
apply (mu_monotonic e); auto.
Qed.

Lemma ok_eq_compat : forall (A:Type) (p p':U) (e e':distr A) (q q':A->U),
    p' == p ->  (feq q q') -> eq_distr e e' -> ok p e q -> ok p' e' q'.
unfold ok; intros.
apply Ule_trans with p; auto.
apply Ule_trans with (mu e q); auto.
apply Ule_trans with (mu e' q); auto.
apply (mu_monotonic e'); auto.
Qed.

Lemma okfun_le_compat : forall (A B:Type) (p p':A -> U) (e:A -> distr B) (q q':A->B->U),
    fle p' p -> (forall x,fle (q x) (q' x)) -> okfun p e q -> okfun p' e q'.
unfold okfun; intros.
apply ok_le_compat with (p x) (q x); auto.
Qed.

Lemma ok_mult : forall (A:Type)(k p:U)(e:distr A)(f : A -> U), ok p e f -> ok (k*p) e (fmult k f).
unfold ok; intros A k p e f oka.
rewrite (mu_stable_mult e k f).
apply Umult_le_compat_right; trivial.
Qed.

Lemma ok_inv :   forall (A:Type)(p:U)(e:distr A)(f : A -> U), ok p e f -> mu e (finv f) <= [1-]p.
unfold ok; intros A p e f oka.
apply Ule_trans with ([1-](mu e f)); auto.
Qed.

Lemma okup_le_compat : forall (A:Type) (p p':U) (e:distr A) (q q':A->U),
    p <= p' -> fle q' q -> okup p e q -> okup p' e q'.
unfold okup; intros.
apply Ule_trans with p; auto.
apply Ule_trans with (mu e q); auto.
apply (mu_monotonic e); auto.
Qed.

Lemma okup_eq_compat : forall (A:Type) (p p':U) (e e':distr A) (q q':A->U),
    p == p' ->  (feq q q') -> eq_distr e e' -> okup p e q -> okup p' e' q'.
unfold okup; intros.
apply Ule_trans with p; auto.
apply Ule_trans with (mu e q); auto.
apply Ule_trans with (mu e' q); auto.
apply (mu_monotonic e'); auto.
Qed.

Lemma upfun_le_compat : forall (A B:Type) (p p':A -> U) (e:A -> distr B) (q q':A->B->U),
    fle p p' -> (forall x,fle (q' x) (q x)) -> upfun p e q -> upfun p' e q'.
unfold upfun; intros.
apply okup_le_compat with (p x) (q x); auto.
Qed.

Lemma okup_mult : forall (A:Type)(k p:U)(e:distr A)(f : A -> U), okup p e f -> okup (k*p) e (fmult k f).
unfold okup; intros A k p e f oka.
rewrite (mu_stable_mult e k f).
apply Umult_le_compat_right; trivial.
Qed.


(** ** Basic rules *)
(** *** Rules for application 
 $\bfrac{\ok{r}{a}{p}~~~\forall x, \ok{p(x)}{f(x)}{q}}{\ok{r}{f(a)}{q}}$
 $\bfrac{\up{r}{a}{p}~~~\forall x, \up{p(x)}{f(x)}{q}}{\up{r}{f(a)}{q}}$*)

Lemma apply_rule : forall (A B:Type)(a:(distr A))(f:A->distr B)(r:U)(p:A->U)(q:B->U),
    (ok r a p) -> (okfun p f (fun x => q)) -> ok r (Mlet a f) q.
unfold ok,okfun,Mlet; simpl; intros. 
apply Ule_trans with (mu a p); auto.
unfold star.
apply mu_monotonic; red; auto.
Qed.

Lemma okup_apply_rule : forall (A B:Type)(a:distr A)(f:A->distr B)(r:U)(p:A->U)(q:B->U),
    (okup r a p) -> (upfun p f (fun x => q)) -> okup r (Mlet a f) q.
unfold okup,upfun,Mlet; simpl; intros. 
apply Ule_trans with (mu a p); auto.
unfold star.
apply mu_monotonic; red; auto.
Qed.

(** *** Rules for abstraction *)
Lemma lambda_rule : forall (A B:Type)(f:A->distr B)(p:A->U)(q:A -> B->U),
   (forall x:A, ok (p x) (f x) (q x)) -> okfun p f q.
trivial.
Qed.

Lemma okup_lambda_rule : forall (A B:Type)(f:A->distr B)(p:A->U)(q:A -> B->U),
   (forall x:A, okup (p x) (f x) (q x)) -> upfun p f q.
trivial.
Qed.

(** *** Rule for conditional
  $ \bfrac{\ok{p_1}{e_1}{q}~~~\ok{p_2}{e_2}{q}}
           {\ok{p_1\times \mu(b)(1_{true}) + p_2\times \mu(b)(1_{false})}
               {if~b~then~e_1~else~e_2}{q}}$

 $ \bfrac{\up{p_1}{e_1}{q}~~~\up{p_2}{e_2}{q}}
           {\up{p_1\times \mu(b)(1_{true}) + p_2\times \mu(b)(1_{false})}
               {if~b~then~e_1~else~e_2}{q}}$
*)

Lemma combiok : forall (A:Type) p q (f1 f2 : A -> U), p <= [1-]q -> fplusok (fmult p f1) (fmult q f2).
unfold fplusok, fmult, fle, finv; intros.
apply Ule_trans with p; auto.
apply Ule_trans with ([1-]q); auto.
Qed.
Hint Resolve combiok.

Lemma fmult_fplusok : forall (A:Type) p q (f1 f2 : A -> U), fplusok f1 f2 -> fplusok (fmult p f1) (fmult q f2).
unfold fplusok, fmult, fle, finv; intros.
apply Ule_trans with (f1 x); auto.
apply Ule_trans with ([1-]f2 x); auto.
Qed.
Hint Resolve fmult_fplusok.

Lemma ifok : forall f1 f2, fplusok (fmult f1 ctrue) (fmult f2 cfalse).
intros; apply fmult_fplusok; unfold fplusok,ctrue,cfalse,finv; auto.
Qed.
Hint Resolve ifok.

Lemma Mif_eq : forall (A:Type)(b:(distr bool))(f1 f2:distr A)(q:A->U),
	(mu (Mif b f1 f2) q) == (mu f1 q) * (mu b ctrue) + (mu f2 q) * (mu b cfalse).
intros.
apply Ueq_trans with (mu b (fplus (fmult (mu f1 q) ctrue) (fmult (mu f2 q) cfalse))).
intros; unfold Mif,Mlet,star; simpl.
apply (mu_stable_eq b); red; intro.
unfold fplus,fmult;destruct x; simpl.
setoid_rewrite (Umult_one_right (mu f1 q)); 
setoid_rewrite (Umult_zero_right (mu f2 q)); 
auto.
setoid_rewrite (Umult_zero_right (mu f1 q)); 
setoid_rewrite (Umult_one_right (mu f2 q)); 
auto.
setoid_rewrite (mu_stable_plus b (f:=(fmult (mu f1 q) ctrue))
                                (g:=(fmult (mu f2 q) cfalse))
                (ifok (mu f1 q) (mu f2 q))).
setoid_rewrite (mu_stable_mult b (mu f1 q) ctrue).
setoid_rewrite (mu_stable_mult b (mu f2 q) cfalse); trivial.
Qed.

Lemma ifrule : 
  forall (A:Type)(b:(distr bool))(f1 f2:distr A)(p1 p2:U)(q:A->U),
       ok p1 f1 q -> ok p2 f2 q
       -> ok (p1 * (mu b ctrue) + p2 * (mu b cfalse)) (Mif b f1 f2) q.
unfold ok; intros.
setoid_rewrite (Mif_eq b f1 f2 q).
apply Uplus_le_compat.
apply Umult_le_compat_left; auto.
apply Umult_le_compat_left; auto.
Qed.

Lemma okup_ifrule : 
  forall (A:Type)(b:(distr bool))(f1 f2:distr A)(p1 p2:U)(q:A->U),
       okup p1 f1 q -> okup p2 f2 q
       -> okup (p1 * (mu b ctrue) + p2 * (mu b cfalse)) (Mif b f1 f2) q.
unfold okup; intros.
setoid_rewrite (Mif_eq b f1 f2 q).
apply Uplus_le_compat.
apply Umult_le_compat_left; auto.
apply Umult_le_compat_left; auto.
Qed.


(** *** Rule for fixpoints 
with $\phi(x)=F(\phi)(x)$, $p_i$ an increasing sequence of functions starting from $0$

$\bfrac{\forall f~i, (\forall x, \ok{p_i(x)}{f}{q}) \Ra \forall x, \ok{p_{i+1}(x)}{F(f)(x)}{q}}%
     {\forall x, \ok{\bigcup_i p_i~x}{\phi(x)}{q}}$
*)
Section Fixrule.
Variables A B : Type.

Variable F : (A -> distr B) -> A -> distr B.

Hypothesis F_mon : forall f g : A -> (distr B), 
  (forall x, le_distr (f x) (g x)) -> forall x, le_distr (F f x) (F g x).


Section Ruleseq.
Variable q : A -> B -> U.
Variable p : A -> nat -> U.

Lemma fixrule : 
   (forall x:A, p x O == 0)->
   (forall (i:nat) (f:A->distr B), 
      (okfun (fun x => p x i) f q) -> okfun (fun x => p x (S i))  (fun x => F f x) q)
   -> okfun (fun x => lub (p x)) (Mfix F F_mon) q.
red; intros p0 Hrec.
assert (forall n:nat, 
        (okfun (fun x => (p x n)) (fun x => iter F n x) q)).
induction n; simpl; auto.
repeat red; intros; auto.
red; intros.
apply lub_le; auto.
intro n; apply Ule_trans with (mu (iter F n x) (q x)).
apply (H n).
apply Mfix_le_iter; auto.
Qed.

Lemma fixrule_up_lub : 
   (forall (i:nat) (f:A->distr B), 
      (upfun (fun x => p x i) f q) -> upfun (fun x => p x (S i))  (fun x => F f x) q)
   -> upfun (fun x => lub (p x)) (Mfix F F_mon) q.
repeat red; intros.
unfold Mfix,mu_lub,mu_lub_; simpl.
apply lub_le_stable.
intro n; generalize x; induction n; simpl; intros; auto.
apply (H n (iter F n) IHn x0).
Qed.

Lemma okup_fixrule_glb : 
   (forall (x:A) n, p x (S n) <= p x n)->
   (forall (i:nat) (f:A->distr B), 
       (upfun (fun x => p x i) f q) -> upfun (fun x => p x (S i))  (fun x => F f x) q)
   -> upfun (fun x => glb (p x)) (Mfix F F_mon) q.
red; intros pdecr Hrec x.
assert (forall n:nat, 
        (upfun (fun x => (p x n)) 
        (fun x => (iter F n x)) q)).
induction n; simpl; auto.
repeat red; intros; auto.
red; intros.
unfold Mfix; simpl.
unfold mu_lub_.
apply lub_glb_le; auto.
intros; apply (@muf_mon_succ A B F F_mon n x); auto.
intro n; apply (H n).
Qed.
End Ruleseq.

Lemma okup_fixrule_inv : 
   forall (q : A -> B -> U) (p : A -> U),
   (forall (f:A->distr B), upfun p f q -> upfun p  (fun x => F f x) q)
           -> upfun p (Mfix F F_mon) q.
unfold upfun, okup; intros.
unfold Mfix; simpl; unfold mu_lub_.
apply lub_le.
intro n; generalize x; induction n; simpl; auto.
Qed.


(*
Section Ruleinv.

Variable p : A -> U.
Variable q : A -> B -> U.
Lemma fixruleinv : 
   (forall (f:A-> distr B), (okfun p f q) -> okfun p (fun x => F f x) q)
   -> okfun (fun x => (p x & (mu (Mfix F F_mon x) (f_one B)))) (Mfix F F_mon) q.
red; intros.
assert (forall n:nat, 
        (okfun (fun x => (p x & (mu (iter F n x) (f_one B))))
        (fun x => iter F n x) q)).
induction n; simpl; auto.
repeat red; intros; auto.
repeat red; intros.
repeat red in IHn.
apply lub_le; auto.
intro n; apply Ule_trans with (mu (iter F n x) q).
apply (H0 n).
apply Mfix_le_iter; auto.
Qed.
End Ruleinv.
*)

(** *** Rules using commutation properties *)

Section TransformFix.


Section Fix_muF.
Variable q : A -> B -> U.
Variable muF : (A -> U) -> A -> U.
Hypothesis muF_mon : Fmonotonic muF.

Lemma muF_stable : Fstable muF. 
auto.
Qed.

Definition mu_muF_commute_le  := 
  forall f x, (forall y, le_distr (f y) (Mfix F F_mon y)) -> 
                         mu (F f x) (q x) <= muF (fun y => mu (f y) (q y)) x.
Hint Unfold mu_muF_commute_le.

Section F_muF_results.
Hypothesis F_muF_le : mu_muF_commute_le.

Lemma mu_mufix_le : forall x, mu (Mfix F F_mon x) (q x) <= mufix muF x.
intros; unfold mufix,Mfix,mu_lub; simpl.
unfold mu_lub_.
apply lub_le_stable; intros.
generalize x; induction n; simpl; intros; auto.
apply Ule_trans with (muF (fun y => mu (iter F n y) (q y)) x0).
apply F_muF_le.
repeat red; intros; unfold Mfix, mu_lub,mu_lub_;simpl.
apply le_lub with (f:=fun n => mu (iter F n y) f); auto.
apply muF_mon; auto.
Qed.
Hint Resolve mu_mufix_le.

Lemma muF_le : forall f, (fle (muF f) f) 
      ->  forall x, mu (Mfix F F_mon x) (q x) <= f x.
intros; apply Ule_trans with (mufix muF x); auto.
apply mufix_inv; auto.
Qed.

Hypothesis muF_F_le : 
    forall f x, (forall y, le_distr (f y) (Mfix F F_mon y)) -> 
                        muF (fun y => mu (f y) (q y)) x <= mu (F f x) (q x).

Lemma mufix_mu_le : forall x, mufix muF x <= mu (Mfix F F_mon x) (q x).
intros; unfold mufix,Mfix,mu_lub; simpl.
unfold mu_lub_.
apply lub_le_stable; intros.
generalize x; induction n; simpl; intros; auto.
apply Ule_trans with (muF (fun y => mu (iter F n y) (q y)) x0).
apply muF_mon; auto.
apply muF_F_le.
repeat red; intros; unfold Mfix, mu_lub,mu_lub_;simpl.
apply le_lub with (f:=fun n => mu (iter F n y) f); auto.
Qed.

End F_muF_results.
Hint Resolve mu_mufix_le mufix_mu_le.

Lemma mufix_mu : 
   (forall f x, (forall y, le_distr (f y) (Mfix F F_mon y)) 
          -> mu (F f x) (q x) == muF (fun y => mu (f y) (q y)) x)
   -> forall x, mufix muF x == mu (Mfix F F_mon x) (q x).
intros; apply Ule_antisym; auto.
apply mufix_mu_le; intros; auto.
rewrite (H f x0); auto. 
Qed.
Hint Resolve mufix_mu.
End Fix_muF.

Section Fix_Term.

Definition pterm (x:A) := mu (Mfix F F_mon x) (f_one B).
Variable muFone : (A -> U) -> A -> U.

Hypothesis muF_mon : Fmonotonic muFone.

Hypothesis F_muF_eq_one : 
    forall f x, (forall y, le_distr (f y) (Mfix F F_mon y))
    -> mu (F f x) (f_one B) == muFone (fun y => mu (f y) (f_one B)) x.

Hypothesis muF_cont :  Fcontlub muFone.

Lemma muF_pterm :  feq pterm (muFone pterm).
red; intros; unfold pterm.
rewrite <- (mufix_mu (fun (x:A) => f_one B) muF_mon F_muF_eq_one x).
rewrite mufix_eq; auto.
apply muF_stable; auto.
red; intros; auto.
apply (mufix_mu (fun (x:A) => f_one B) muF_mon F_muF_eq_one x0).
Qed.
Hint Resolve muF_pterm.
End Fix_Term.

Section Fix_muF_Term.

Variable q : A -> B -> U.
Definition qinv x y := [1-]q x y.

Variable muFqinv : (A -> U) -> A -> U.

Hypothesis muF_mon_inv : Fmonotonic muFqinv.

Hypothesis F_muF_le_inv : mu_muF_commute_le qinv muFqinv.

Lemma muF_le_term : forall f, fle (muFqinv (finv f)) (finv f) ->
    forall x, f x & pterm x <= mu (Mfix F F_mon x) (q x).
intros; apply Ule_trans with (mu (Mfix F F_mon x) (fesp (q x) (f_one B))).
apply Ule_trans with ([1-] mu (Mfix F F_mon x) (qinv x) & pterm x).
apply Uesp_le_compat; auto.
apply Uinv_le_perm_right.
apply muF_le with (muF:=muFqinv) (q:=qinv) (f:=finv f) (x:=x); auto.
unfold pterm; replace (qinv x) with (finv (q x)); auto.
apply mu_monotonic; intro; unfold fesp,f_one; repeat Usimpl; auto.
Qed.

Lemma muF_le_term_minus : 
forall f, fle f pterm -> fle (muFqinv (fminus pterm f)) (fminus pterm f) ->
    forall x, f x <= mu (Mfix F F_mon x) (q x).
intros; apply Ule_trans with ((f x + [1-]pterm x) & pterm x).
red in H; rewrite Uplus_inv_esp_simpl; auto.
apply muF_le_term with (f:=fun y => f y + [1-]pterm y); auto.
apply fle_trans with (muFqinv (fminus pterm f)).
apply muF_mon_inv; unfold fle, fminus, finv; auto.
apply fle_trans with (fminus pterm f); auto.
unfold fle, fminus, Uminus, finv; auto.
Qed.

Variable muFq : (A -> U) -> A -> U.

Hypothesis muF_mon : Fmonotonic muFq.

Hypothesis F_muF_le : mu_muF_commute_le q muFq.

Lemma muF_eq : forall f, fle (muFq f) f -> fle (muFqinv (finv f)) (finv f)-> 
    forall x, pterm x == 1 -> mu (Mfix F F_mon x) (q x) == f x.
intros; apply Ule_antisym.
apply muF_le with (muF:=muFq); auto.
apply Ule_trans with (f x & pterm x).
rewrite H1; auto.
apply muF_le_term; auto.
Qed.

End Fix_muF_Term.
End TransformFix.


Section LoopRule.
Variable q : A -> B -> U.
Variable stop : A -> distr bool.
Variable step : A -> distr A.
Variable a : U.

Definition Loop (f:A->U) (x:A) : U:= 
     mu (stop x) (fun b => if b then a else mu (step x) f).

Fixpoint loopn (n:nat)(x:A){struct n}  : U := 
    match n with O => 0
                       | S p => Loop (loopn p) x
    end.

Definition loop (x:A) : U := lub (fun n => loopn n x).

Lemma Mfixvar : 
  (forall (f:A->distr B), 
      okfun (fun x => Loop (fun y => mu (f y) (q y)) x)  (fun x => F f x) q)
 -> okfun loop (Mfix F F_mon) q.
intros; unfold loop; simpl.
apply fixrule with (p:=fun x n => loopn n x); simpl; intros;auto.
unfold okfun,ok in *|-*.
intro x; apply Ule_trans with (2:=H f x).
unfold Loop; simpl; auto.
apply (mu_monotonic (stop x)); red; intros.
case x0; auto.
apply (mu_monotonic (step x)); red; auto.
Qed.

Fixpoint up_loopn (n:nat)(x:A){struct n}  : U := 
    match n with O => 1
                       | S p => Loop (up_loopn p) x
    end.

Definition up_loop (x:A) : U := glb (fun n => up_loopn n x).

Lemma Mfixvar_up : 
  (forall (f:A->distr B), 
      upfun (fun x => Loop (fun y => mu (f y) (q y)) x)  (fun x => F f x) q)
 -> upfun up_loop (Mfix F F_mon) q.
intros; unfold up_loop; simpl.
apply okup_fixrule_glb with (p:=fun x n => up_loopn n x); simpl; intros;auto.
unfold upfun,okup in *|-*.
generalize x; induction n; simpl; intros; auto.
unfold Loop; simpl; auto.
apply mu_monotonic.
red; intros.
destruct x1; auto.
apply mu_monotonic; auto.
intro x.
red; apply Ule_trans with (1:=H f x).
unfold Loop; simpl; auto.
apply (mu_monotonic (stop x)); red; intros.
case x0; auto.
apply (mu_monotonic (step x)); red; auto.
Qed.

End LoopRule.

End Fixrule.

(** ** Rules for intervals *)
(** Distributions operates on intervals *)

Definition Imu : forall A:Type, distr A-> (A->IU) -> IU.
intros A m F; exists (mu m (fun x => low (F x))) (mu m (fun x => up (F x))).
apply mu_monotonic; auto.
Defined.

Lemma low_Imu : forall (A:Type) (e:distr A) (F: A -> IU),
             low (Imu e F) = mu e (fun x => low (F x)).
trivial.
Qed.

Lemma up_Imu : forall (A:Type) (e:distr A) (F: A -> IU),
             up (Imu e F) = mu e (fun x => up (F x)).
trivial.
Qed.

Lemma Imu_monotonic : forall (A:Type) (e:distr A) (F G : A -> IU),
            (forall x, Iincl (F x) (G x)) -> Iincl (Imu e F) (Imu e G).
unfold Iincl,Imu; simpl; intuition.
apply mu_monotonic; firstorder.
apply mu_monotonic; firstorder.
Qed.

Lemma Imu_stable_eq : forall (A:Type) (e:distr A) (F G : A -> IU),
            (forall x, Ieq (F x) (G x)) -> Ieq (Imu e F) (Imu e G).
unfold Ieq,Imu; simpl; intuition.
apply mu_stable_eq; firstorder.
apply mu_stable_eq; firstorder.
Qed.
Hint Resolve Imu_monotonic Imu_stable_eq.

Lemma Imu_singl : forall (A:Type) (e:distr A) (f:A->U),
           Ieq (Imu e (fun x => singl (f x))) (singl (mu e f)).
unfold Ieq,Imu,singl; simpl; intuition.
Qed.

Lemma Imu_inf : forall (A:Type) (e:distr A) (f:A->U),
           Ieq (Imu e (fun x => inf (f x))) (inf (mu e f)).
unfold Ieq,Imu,inf; simpl; intuition.
exact (mu_zero e).
Qed.

Lemma Imu_sup : forall (A:Type) (e:distr A) (f:A->U),
           Iincl (Imu e (fun x => sup (f x))) (sup (mu e f)).
unfold Iincl,Imu,inf; simpl; intuition.
Qed.

Lemma Iin_mu_Imu : 
   forall (A:Type) (e:distr A) (F:A->IU) (f:A->U),
           (forall x, Iin (f x) (F x)) -> Iin (mu e f) (Imu e F).
unfold Iin,Imu; simpl; split.
apply mu_monotonic; firstorder.
apply mu_monotonic; firstorder.
Qed.
Hint Resolve Iin_mu_Imu.

Definition Iok (A:Type) (I:IU) (e:distr A) (F:A->IU) := Iincl (Imu e F) I.
Definition Iokfun (A B:Type)(I:A->IU) (e:A->distr B) (F:A->B->IU) 
               := forall x, Iok (I x) (e x) (F x).

Lemma Iin_mu_Iok : 
   forall (A:Type) (I:IU) (e:distr A) (F:A->IU) (f:A->U),
           (forall x, Iin (f x) (F x)) -> Iok I e F -> Iin (mu e f) I.
intros; apply Iincl_in with (Imu e F); auto.
Qed.


(** *** Stability *)
Lemma Iok_le_compat : forall (A:Type) (I J:IU) (e:distr A) (F G:A->IU),
   Iincl I J -> (forall x, Iincl (G x) (F x)) -> Iok I e F -> Iok J e G.
unfold Iok; intros; apply Iincl_trans with I; auto.
apply Iincl_trans with (Imu e F); auto.
Qed.

Lemma Iokfun_le_compat : forall (A B:Type) (I J:A->IU) (e:A->distr B) (F G:A->B->IU),
   (forall x, Iincl (I x) (J x)) -> (forall x y, Iincl (G x y) (F x y)) -> Iokfun I e F -> Iokfun J e G.
unfold Iokfun; intros; apply Iok_le_compat with (I x) (F x); auto.
Qed.

(** *** Rule for values *)

Lemma Iunit_eq : forall (A: Type) (a:A) (F:A->IU), Ieq (Imu (Munit a) F) (F a).
intros; unfold Ieq,Imu,Munit; simpl; auto.
Qed.


(** *** Rule for application *)

Lemma Ilet_eq : forall (A B : Type) (a:distr A) (f:A->distr B)(I:IU)(G:B->IU),
   Ieq (Imu (Mlet a f) G) (Imu a (fun x => Imu (f x) G)).
unfold Ieq,Imu,Mlet,Iincl; simpl; intuition. 
Qed.
Hint Resolve Ilet_eq.

Lemma Iapply_rule : forall (A B : Type) (a:distr A) (f:A->distr B)(I:IU)(F:A->IU)(G:B->IU),
    Iok I a F -> Iokfun F f (fun x => G) -> Iok I (Mlet a f) G.
unfold Iokfun,Iok;intros.
apply Ieq_incl_trans with (Imu a (fun x => Imu (f x) G)); auto.
apply Iincl_trans with (Imu a F); auto.
Qed.

(** *** Rule for abstraction *)
Lemma Ilambda_rule : forall (A B:Type)(f:A->distr B)(F:A->IU)(G:A -> B->IU),
   (forall x:A, Iok (F x) (f x) (G x)) -> Iokfun F f G.
trivial.
Qed.


(** *** Rule for conditional *)

Lemma Imu_Mif_eq : forall (A:Type)(b:distr bool)(f1 f2:distr A)(F:A->IU),
 Ieq (Imu (Mif b f1 f2) F) (Iplus (Imultk (mu b ctrue) (Imu f1 F)) (Imultk (mu b cfalse) (Imu f2 F))).
red; intros.
rewrite low_Imu; rewrite up_Imu.
repeat rewrite Mif_eq.
repeat rewrite low_Iplus; repeat rewrite low_Imultk.
repeat rewrite up_Iplus; repeat rewrite up_Imultk.
repeat rewrite low_Imu; repeat rewrite up_Imu; auto.
Qed.

Lemma Iifrule : 
  forall (A:Type)(b:(distr bool))(f1 f2:distr A)(I1 I2:IU)(F:A->IU),
       Iok I1 f1 F -> Iok I2 f2 F
       -> Iok (Iplus (Imultk (mu b ctrue) I1) (Imultk (mu b cfalse) I2)) (Mif b f1 f2) F.
unfold Iok; intros.
apply Ieq_incl_trans with (1:=Imu_Mif_eq b f1 f2 F).
split.
repeat rewrite low_Iplus; repeat rewrite low_Imultk.
apply Uplus_le_compat; auto.
repeat rewrite up_Iplus; repeat rewrite up_Imultk.
apply Uplus_le_compat; auto.
Qed.

(** *** Rule for fixpoints 
with $\phi(x)=F(\phi)(x)$, $p_i$ an decreasing sequence of intervals functions ($p_{i+1}(x)\subseteq p_i(x)$) such that $p_0(x)$ contains $0$ for all $x$.

$\bfrac{\forall f~i, (\forall x, \iok{p_i(x)}{f}{q~x}) \Ra \forall x, \iok{p_{i+1}(x)}{F(f)(x)}{q~x}}%
     {\forall x, \iok{\bigcap_i p_i~x}{\phi(x)}{q~x}}$
*)
Section IFixrule.
Variables A B : Type.

Variable F : (A -> distr B) -> A -> distr B.

Hypothesis F_mon : forall f g : A -> (distr B), 
  (forall x, le_distr (f x) (g x)) -> forall x, le_distr (F f x) (F g x).

Section IRuleseq.
Variable Q : A -> B -> IU.

Variable I : A -> nat -> IU.
Hypothesis decrp : forall x n, Iincl (I x (S n)) (I x n).

Lemma Ifixrule : 
   (forall x:A, Iin 0 (I x O)) ->
   (forall (i:nat) (f:A->distr B), 
      (Iokfun (fun x => I x i) f Q) -> Iokfun (fun x => I x (S i))  (fun x => F f x) Q)
   -> Iokfun (fun x => lim (I x) (decrp x)) (Mfix F F_mon) Q.
red; intros p0 Hrec.
assert (forall n:nat, 
        (Iokfun (fun x => (I x n)) (fun x => iter F n x) Q)).
induction n; simpl; auto.
split.
rewrite low_lim; rewrite low_Imu.
apply lub_le; auto.
intro n; apply Ule_trans with (low (Imu (iter F n x) (Q x))).
case (H n x); auto.
rewrite low_Imu; apply Mfix_le_iter; auto.
rewrite up_lim; rewrite up_Imu.
unfold Mfix,mu_lub,mu_lub_; simpl.
apply lub_glb_le; intros; auto.
apply (@muf_mon_succ A B F F_mon n x); auto.
case (H n x); auto.
Qed.
End IRuleseq.

Section ITransformFix.

Section IFix_muF.
Variable Q : A -> B -> IU.
Variable ImuF : (A -> IU) -> A -> IU.
Hypothesis ImuF_mon : forall I J, 
      (forall x, Iincl (I x) (J x)) -> forall x, Iincl (ImuF I x) (ImuF J x).

Lemma ImuF_stable : forall I J, 
      (forall x, Ieq (I x) (J x)) -> forall x, Ieq (ImuF I x) (ImuF J x).
intros; apply Iincl_antisym; auto.
Qed.

Section IF_muF_results.
Hypothesis Iincl_F_ImuF : 
    forall f x, (forall y, le_distr (f y) (Mfix F F_mon y)) -> 
                      Iincl (Imu (F f x) (Q x)) (ImuF (fun y => Imu (f y) (Q y)) x).

Lemma Iincl_fix_ifix : forall x, Iincl (Imu (Mfix F F_mon x) (Q x)) (Ifix ImuF ImuF_mon x). 
assert (forall n x, Iincl (Imu (iter F n x) (Q x)) (Iiter ImuF n x)).
induction n; simpl; intros; auto.
apply Iincl_trans with (ImuF (fun y => Imu (iter F n y) (Q y)) x).
apply Iincl_F_ImuF.
repeat red; intros; unfold Mfix, mu_lub,mu_lub_;simpl.
apply le_lub with (f:=fun n => mu (iter F n y) f); auto.
apply ImuF_mon; auto.
intros; unfold Iincl, Ifix,Imu,Mfix,mu_lub; simpl.
unfold mu_lub_; split.
apply lub_le_stable; intros.
case (H n x); intros.
apply Ule_trans with (low (Imu (iter F n x) (Q x))); auto.
apply lub_glb_le; intros; auto.
apply (@muf_mon_succ A B F F_mon n x).
case (Iiter_decr ImuF ImuF_mon x n); auto.
case (H n x); intros.
apply Ule_trans with (up (Imu (iter F n x) (Q x))); auto.
Qed.
Hint Resolve Iincl_fix_ifix.

(*
Hypothesis Iincl_ImuF_F : 
    forall f x, (forall y, le_distr (f y) (Mfix F F_mon y)) -> 
                      Iincl (ImuF (fun y => Imu (f y) (Q y)) x) (Imu (F f x) (Q x)).

Lemma Iincl_ifix_fix : forall x, Iincl (Ifix ImuF ImuF_mon x) (Imu (Mfix F F_mon x) (Q x)) . 
assert (forall n x, Iincl (Iiter ImuF n x) (Imu (iter F n x) (Q x))).
induction n; simpl; intros; auto.
apply Iincl_trans with (ImuF (fun y => Imu (iter F n y) (Q y)) x).
apply IF_muF_incl.
repeat red; intros; unfold Mfix, mu_lub,mu_lub_;simpl.
apply le_lub with (f:=fun n => mu (iter F n y) f); auto.
apply ImuF_mon; auto.
intros; unfold Iincl, Ifix,Imu,Mfix,mu_lub; simpl.
unfold mu_lub_; split.
apply lub_le_stable; intros.
case (H n x); intros.
apply Ule_trans with (low (Imu (iter F n x) (Q x))); auto.
apply lub_glb_le; intros; auto.
apply (@muf_mon_succ A B F F_mon n x).
case (Iiter_decr ImuF ImuF_mon x n); auto.
case (H n x); intros.
apply Ule_trans with (up (Imu (iter F n x) (Q x))); auto.
Qed.
Hint Resolve Iincl_fix_mu.

Lemma Iincl_ImuF : forall f, (forall x, Iincl (f x) (ImuF f x)) -> forall x, Iincl (Imu (Mfix F F_mon x) (Q x)) (f x).
intros; apply Iincl_trans with (Ifix ImuF ImuF_mon x); auto.
apply Iincl_inv; auto.
Qed.

Hypothesis muF_F_le : 
    forall f x, (forall y, le_distr (f y) (Mfix F F_mon y)) -> 
                        muF (fun y => mu (f y) (q y)) x <= mu (F f x) (q x).

Lemma mufix_mu_le : forall x, mufix muF x <= mu (Mfix F F_mon x) (q x).
intros; unfold mufix,Mfix,mu_lub; simpl.
unfold mu_lub_.
apply lub_le_stable; intros.
generalize x; induction n; simpl; intros; auto.
apply Ule_trans with (muF (fun y => mu (iter F n y) (q y)) x0).
apply muF_mon; auto.
apply muF_F_le.
repeat red; intros; unfold Mfix, mu_lub,mu_lub_;simpl.
apply le_lub with (f:=fun n => mu (iter F n y) f); auto.
Qed.

End F_muF_results.
Hint Resolve mu_mufix_le mufix_mu_le.

Lemma mufix_mu : 
   (forall f x, (forall y, le_distr (f y) (Mfix F F_mon y)) 
          -> mu (F f x) (q x) == muF (fun y => mu (f y) (q y)) x)
   -> forall x, mufix muF x == mu (Mfix F F_mon x) (q x).
intros; apply Ule_antisym; auto.
apply mufix_mu_le; intros; auto.
rewrite (H f x0); auto. 
Qed.
Hint Resolve mufix_mu.
End Fix_muF.

Section Fix_Term.

Definition pterm (x:A) := mu (Mfix F F_mon x) (f_one B).
Variable muF : (A -> U) -> A -> U.

Hypothesis muF_mon : Fmonotonic muF.

Hypothesis F_muF_eq_one : 
    forall f x, (forall y, le_distr (f y) (Mfix F F_mon y))
    -> mu (F f x) (f_one B) == muF (fun y => mu (f y) (f_one B)) x.

Hypothesis muF_cont :  Fcontlub muF.

Lemma muF_pterm :  feq pterm (muF pterm).
red; intros; unfold pterm.
rewrite <- (mufix_mu (fun (x:A) => f_one B) muF_mon F_muF_eq_one x).
rewrite mufix_eq; auto.
apply muF_stable; auto.
red; intros; auto.
apply (mufix_mu (fun (x:A) => f_one B) muF_mon F_muF_eq_one x0).
Qed.
Hint Resolve muF_pterm.
End Fix_Term.

Section Fix_muF_Term.

Variable muF : (A -> B -> U) -> (A -> U) -> A -> U.

Hypothesis muF_mon : forall q, Fmonotonic (muF q).

Variable q : A -> B -> U.
Definition qinv x y := [1-]q x y.

Hypothesis F_muF_le_inv : 
    forall f x, (forall y, le_distr (f y) (Mfix F F_mon y))
    -> mu (F f x) (qinv x) <= muF qinv (fun y => mu (f y) (qinv y)) x.

Lemma muF_le_term : forall f, fle (muF qinv (finv f)) (finv f) ->
    forall x, f x & pterm x <= mu (Mfix F F_mon x) (q x).
intros; apply Ule_trans with (mu (Mfix F F_mon x) (fesp (q x) (f_one B))).
apply Ule_trans with ([1-] mu (Mfix F F_mon x) (qinv x) & pterm x).
apply Uesp_le_compat; auto.
apply Uinv_le_perm_right.
apply muF_le with (muF:=muF qinv) (q:=qinv) (f:=finv f) (x:=x); auto.
unfold pterm; replace (qinv x) with (finv (q x)); auto.
apply mu_monotonic; intro; unfold fesp,f_one; repeat Usimpl; auto.
Qed.

Hypothesis F_muF_le : 
    forall f x, (forall y, le_distr (f y) (Mfix F F_mon y))
    -> mu (F f x) (q x) <= muF q (fun y => mu (f y) (q y)) x.

Lemma muF_eq : forall f, fle (muF q f) f -> fle (muF qinv (finv f)) (finv f)-> 
    forall x, pterm x == 1 -> mu (Mfix F F_mon x) (q x) == f x.
intros; apply Ule_antisym.
apply muF_le with (muF:=muF q); auto.
apply Ule_trans with (f x & pterm x).
rewrite H1; auto.
apply muF_le_term; auto.
Qed.

End Fix_muF_Term.

*)
End IF_muF_results.

End IFix_muF.
End ITransformFix.
End IFixrule.



(** ** Rules for [Flip] *)

Lemma Flip_ctrue : mu Flip ctrue == [1/2].
unfold Flip; auto.
Qed.

Lemma Flip_cfalse : mu Flip cfalse == [1/2].
unfold Flip; auto.
Qed.

Lemma ok_Flip :   forall q : bool -> U, ok ([1/2] * q true + [1/2] * q false) Flip q.
red; unfold Flip, flip; simpl; auto.
Qed.

Lemma okup_Flip :   forall q : bool -> U, okup ([1/2] * q true + [1/2] * q false) Flip q.
red; unfold Flip, flip; simpl; auto.
Qed.

Hint Resolve ok_Flip okup_Flip Flip_ctrue Flip_cfalse.

Lemma Flip_eq : forall q : bool -> U, mu Flip q == [1/2] * q true + [1/2] * q false.
intros; apply Ule_antisym; auto.
Qed.
Hint Resolve Flip_eq.

Lemma IFlip_eq : forall Q : bool -> IU, Ieq (Imu Flip Q) (Iplus (Imultk [1/2] (Q true)) (Imultk [1/2] (Q false))).
red; unfold Flip, flip; simpl; auto.
Qed.
Hint Resolve IFlip_eq.

(** ** Rules for total (well-founded) fixpoints *)

Section Wellfounded.
Variables A B : Type.
Variable R : A -> A -> Prop.
Hypothesis Rwf : well_founded R.
Variable F : forall x, (forall y, R y x -> distr B) -> distr B.

Definition WfFix : A -> distr B := Fix Rwf (fun _ => distr B) F.

Hypothesis Fext : forall x f g, (forall y (p:R y x), eq_distr (f y p) (g y p)) -> eq_distr (F f) (F g).

Lemma Acc_iter_distr : 
   forall x, forall r s : Acc R x, eq_distr (Acc_iter (fun _=> distr B) F r) (Acc_iter  (fun _=> distr B) F s).
intros x r; elim r using Acc_inv_dep; simpl; intros.
case s; simpl; intros.
apply Fext; auto.
Qed.

Lemma WfFix_eq : forall x, eq_distr (WfFix x) (F (fun (y:A) (p:R y x) => WfFix y)).
intro x; unfold WfFix,Fix.
case (Rwf x); simpl; intros.
apply Fext; intros.
apply Acc_iter_distr.
Qed.

Variable P : distr B -> Prop.
Hypothesis Pext : forall m1 m2, eq_distr m1 m2 -> P m1 -> P m2.

Lemma WfFix_ind : 
     (forall x f, (forall y (p:R y x), P (f y p)) -> P (F f)) 
  -> forall x, P (WfFix x).
intros; pattern x; apply well_founded_ind with (R:=R); trivial; intros.
apply Pext with (m1:=  F (fun (y:A) (p:R y x0) => WfFix y)).
apply eq_distr_sym; apply WfFix_eq.
apply H; auto.
Qed.

End Wellfounded.

End Rules.
