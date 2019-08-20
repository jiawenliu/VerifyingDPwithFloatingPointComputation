(** * Libwp.v : Partial correctness *)
Require Export Carac.
Set Implicit Arguments.

Module Liberal (Univ:Universe).
Import Univ.

Module CP := (CaracFun Univ).
Import CP.
Import CP.RP.
Import CP.RP.PP.
Import CP.RP.PP.MP.
Import CP.RP.PP.MP.UP.

Section LibDefProp.
Variable A : Type.

(** ** Definition and basic properties *)

Definition lib (m:distr A) : M A := fun f => [1-] (mu m (finv f)).

Lemma le_mu_lib : forall m f, mu m f <= lib m f.
unfold lib; intros.
apply Ule_trans with (mu m (finv (finv f))).
apply mu_monotonic; unfold finv; auto.
apply mu_stable_inv; auto.
Qed.

Lemma lib_one : forall m, 1 <= lib m (f_one A).
unfold lib; intros.
apply Ule_trans with ([1-] mu m (f_zero A)).
rewrite mu_zero; auto.
apply Uinv_le_compat; apply mu_monotonic; unfold finv,f_one,f_zero; auto.
Qed.

Lemma lib_inv : forall m f,  lib m (finv f) == [1-]mu m f.
unfold lib; intros.
Usimpl.
apply (mu_stable_eq m); unfold finv; auto.
Qed.

Lemma lib_monotonic : forall m, monotonic (lib m).
red; unfold lib; intros; Usimpl.
apply (mu_monotonic m).
unfold fle,finv; auto.
Qed.

Hint Resolve lib_one lib_inv lib_monotonic le_mu_lib.

Lemma lib_stable_eq : forall m, stable_eq (lib m).
auto.
Qed.
Hint Resolve lib_stable_eq.

Lemma mu_lib_le_esp : forall m f g, lib m f & mu m g <= mu m (fesp f g).
unfold lib; intros.
rewrite Uesp_sym.
apply Uplus_inv_le_esp; Usimpl.
apply Ule_trans with (mu m (fplus (fesp f g) (finv f))); auto.
apply (mu_monotonic m); unfold fplus, fle, fesp,finv; intros; auto.
rewrite Uesp_sym; auto.
Qed.
Hint Resolve mu_lib_le_esp.

Lemma le_lib_mu : forall m f, lib m f & mu m (f_one A) <= mu m f.
intros; apply Ule_trans with (mu m (fesp f (f_one A))); auto.
apply (mu_monotonic m); unfold fle,fesp,f_one; auto.
Qed.
Hint Resolve le_lib_mu.

Lemma lib_le_esp : forall m f g, lib m f & lib m g <= lib m (fesp f g).
intros; unfold lib.
rewrite <- Uinv_plus_esp; Usimpl.
apply Ule_trans with (mu m (fplus (finv f) (finv g))); auto.
apply (mu_monotonic m); unfold fle,fesp,finv; auto.
Qed.
Hint Resolve lib_le_esp.

Lemma lib_plus_left : forall m f g, fplusok f g -> lib m (fplus f g) == lib m f + mu m g.
intros; unfold lib.
setoid_replace (mu m (finv f)) with (mu m (finv (fplus f g)) + mu m g).
rewrite Uinv_plus_right; auto.
apply Ule_trans with ([1-]mu m (finv g)); try Usimpl; auto.
apply mu_monotonic; auto.
apply Ueq_trans with (mu m (fplus (finv (fplus f g)) g)).
apply mu_stable_eq; unfold fplusok,fle,finv in H; 
unfold feq,fplus,finv; intros.
rewrite Uinv_plus_right; auto.
apply (mu_stable_plus m); auto.
Qed.

Lemma lib_plus_right : forall m f g, fplusok f g -> lib m (fplus f g) == mu m f + lib m g.
intros; apply Ueq_trans with (lib m (fplus g f)).
apply lib_stable_eq.
red; unfold fplus; auto.
apply Ueq_trans with (lib m g + mu m f); auto.
apply lib_plus_left; auto.
Qed.

Definition okl (p : U) (m : distr A) (q : A -> U) := p <= lib m q.
  
End LibDefProp.
Hint Resolve lib_one lib_inv lib_monotonic le_mu_lib lib_stable_eq 
                    mu_lib_le_esp le_lib_mu lib_le_esp lib_plus_left lib_plus_right.


(** ** Rules for liberal constructions of programs *)
Section Programs.
Variables A B: Type.

Lemma lib_unit : forall (x:A) (p : A -> U), lib (Munit x) p == p x.
intros; compute; auto.
Qed.

Lemma lib_let : forall (m : distr A) (M : A -> distr B) (p : B -> U), 
        lib (Mlet m M) p == lib m (fun x => lib (M x) p).
intros; compute; Usimpl.
destruct m.
apply (monotonic_stable_eq mu_monotonic0); auto.
Qed.

Lemma lib_if : forall (mb:distr bool) (m1 m2 : distr A) (p : A -> U), 
        lib (Mif mb m1 m2) p == lib mb (fun b => if b then lib m1 p else lib m2 p).
intros; compute; Usimpl.
destruct mb.
apply (monotonic_stable_eq mu_monotonic0).
red; destruct x; auto.
Qed.

(** *** Rules for liberal fixpoints 
with $\phi(x)=F(\phi)(x)$, 

$\bfrac{\forall f, (\forall x, \okl{p(x)}{f}{q}) \Ra \forall x, \okl{p(x)}{F(f)(x)}{q}}%
     {\forall x, \okl{p~x}{\phi(x)}{q}}$
*)
Section Fixrules.

Definition oklfun (p : A->U) (m : A->distr B) (q : A -> B-> U) := 
     forall x, p x <= lib (m x) (q x).

Definition uplfun (p : A->U) (m : A->distr B) (q : A -> B-> U) := 
     forall x, lib (m x) (q x) <= p x.

Variable F : (A -> distr B) -> A -> distr B.

Hypothesis F_mon : forall f g : A -> (distr B), 
  (forall x, le_distr (f x) (g x)) -> forall x, le_distr (F f x) (F g x).

Lemma libfixrule : 
   forall p q,
   (forall (f:A->distr B), oklfun p f q -> oklfun p (fun x => F f x) q)
   -> oklfun p (Mfix F F_mon) q.
unfold oklfun,lib; intros.
apply Uinv_le_perm_right.
unfold Mfix; simpl; unfold mu_lub_.
apply lub_le.
intro n; generalize x; induction n; simpl; auto.
Qed.

Section UplibFixRule.
Variable p : A -> nat -> U.
Hypothesis p1 : forall x, p x O == 1.
Variable q : A -> B -> U.

Lemma up_libfixrule : 
   (forall (i:nat)(f:A->distr B), uplfun (fun x => p x i) f q 
                                        -> uplfun (fun x => p x (S i)) (fun x => F f x) q)
   -> uplfun (fun x => glb (p x)) (Mfix F F_mon) q.
red; intros.
assert (forall n:nat, 
        (uplfun (fun x => (p x n)) 
        (fun x => (iter F n x)) q)).
induction n; simpl; auto.
repeat red; intros; auto.
rewrite p1; auto.
unfold lib, glb; Usimpl.
apply lub_le; auto.
intro n; apply Ule_trans with (mu (iter F n x) (finv (q x))).
unfold uplfun, lib in H0.
apply Uinv_le_perm_left.
apply (H0 n).
apply Mfix_le_iter; auto.
Qed.

End UplibFixRule.

(** ** Case the post-expectation is transformed in a functorial way *)

(** *** Invariant rules *)

Section Fix_nuF. 


Variable nuF :  (A -> U) -> A -> U.

Hypothesis nuF_mon : Fmonotonic nuF.

Variable q : A -> B -> U.

Lemma nuF_stable : Fstable nuF.
auto.
Qed.

Hypothesis F_nuF_eq : 
    forall f x, lib (F f x) (q x) == nuF (fun y => lib (f y) (q y)) x.

Lemma nufix_lib : forall x, nufix nuF x == lib (Mfix F F_mon x) (q x).
intros; unfold nufix, lib.
unfold glb; Usimpl.
unfold Mfix; simpl.
unfold mu_lub_.
apply lub_eq_stable; intros.
generalize x; induction n; simpl; intros; auto.
apply Uinv_eq_perm_left.
rewrite (F_nuF_eq (iter F n) x0).
apply nuF_stable.
repeat red; unfold lib; auto.
Qed.
Hint Resolve nufix_lib.

Lemma nuF_le : forall f, fle f (nuF f) 
        -> forall x, f x <= lib (Mfix F F_mon x) (q x).
intros; apply Ule_trans with (nufix nuF x); auto.
apply nufix_inv; auto.
Qed.

Lemma nuF_muF_le : forall f, fle f (nuF f) 
     -> forall x, f x & pterm F F_mon x <= mu (Mfix F F_mon x) (q x).
intros; apply Ule_trans with (lib (Mfix F F_mon x) (q x) & pterm F F_mon x).
apply Uesp_le_compat;auto.
apply  nuF_le; auto.
apply Ule_trans with (mu (Mfix F F_mon x) (fesp (q x) (f_one B))).
unfold pterm; auto.
apply mu_monotonic; auto.
Qed.
Hint Resolve nuF_muF_le.


Lemma muF_pterm_le : 
          forall f, fle (fplus f (finv (pterm F F_mon))) (nuF (fplus f (finv (pterm F F_mon)))) 
     -> fle f (pterm F F_mon) -> forall x, f x <= mu (Mfix F F_mon x) (q x).
intros; apply Ule_trans with ((f x + [1-](pterm F F_mon x)) & pterm F F_mon x).
rewrite (Uplus_inv_esp_simpl); auto.
apply nuF_muF_le with (f:= fun x => f x + [1-] pterm F F_mon x); auto.
Qed.

End Fix_nuF. 


(** *** Case nuF is parametric in q *)
Variable nuF : (A->B->U) -> (A -> U) -> A -> U.
Hypothesis nuF_mon : forall q, Fmonotonic (nuF q).

Hypothesis nuF_q_monotonic : 
    forall q1 q2 f, (forall x y, q1 x y <= q2 x y) -> fle (nuF q1 f)  (nuF q2 f).

Lemma nuF_q_eq_stable : 
    forall q1 q2 f, (forall x y, q1 x y == q2 x y) -> feq (nuF q1 f) (nuF q2 f).
auto.
Qed.

Variable muF : (A->B->U) -> (A -> U) -> A -> U.

Hypothesis muF_mon : forall q, Fmonotonic (muF q).

Hypothesis nuF_plus : forall q1 q2 f1 f2,
     feq (nuF (fun x y => q1 x y + q2 x y)  (fplus f1 f2)) (fplus (muF q1 f1) (nuF q2 f2)).

Hypothesis nuF_mult : forall a q f,
           feq (nuF  (fun x y => a * (q x y)) (fmult a f)) (fmult a (nuF q f)).

Hypothesis nuF_inv : forall q f,
           feq (nuF  (fun x y => [1-](q x y)) (finv f)) (finv (muF q f)).

Hypothesis muF_mult : forall a q f,
           feq (muF  (fun x y => a * (q x y)) (fmult a f)) (fmult a (muF q f)).

Hypothesis muF_q_monotonic : 
    forall q1 q2 f, (forall x y, q1 x y <= q2 x y) -> fle (muF q1 f) (muF q2 f).

Hypothesis F_muF_eq_one : 
    forall f x, (forall y, le_distr (f y) (Mfix F F_mon y)) -> mu (F f x) (f_one B) == muF (fun (x:A) => f_one B) (fun y => mu (f y) (f_one B)) x.

Hypothesis F_nuF_eq_one : 
    forall f x, (forall y, le_distr (f y) (Mfix F F_mon y)) -> lib (F f x) (f_one B) == nuF (fun (x:A) => f_one B) (fun y => lib (f y) (f_one B)) x.

Hypothesis muF_cont :  Fcontlub (muF (fun (x:A) => f_one B)).

Section InvariantTerm.

Variable q : A -> B -> U.

Hypothesis F_nuF_eq : 
    forall f x, lib (F f x) (q x) == nuF q (fun y => lib (f y) (q y)) x.

Lemma muF_pterm_le_inv : 
          forall f, fle f (muF q f) 
          -> fle f (pterm F F_mon) -> forall x, f x <= mu (Mfix F F_mon x) (q x).
intros; apply (muF_pterm_le (nuF:=nuF q)); intros; auto.
rewrite (nuF_q_eq_stable q (fun (x: A) (y: B) => q x y + 0)); auto.
rewrite (nuF_plus q (fun x y => 0)).
apply fplus_fle_compat; auto.
rewrite (nuF_q_eq_stable (fun (x: A) (y: B) => 0) (fun (x: A) (y: B) => [1-]1)); auto.
rewrite (nuF_inv (fun (x:A)(y:B)=>1) (pterm F F_mon)).
apply finv_fle_compat.
apply feq_fle_sym.
apply (muF_pterm  (muF_mon (fun (x:A) => f_one B)) F_muF_eq_one muF_cont); auto.
Qed.

End InvariantTerm.

Lemma muF_pterm_le_mult : 
          forall a f,  fle f (muF (fun (x:A) (y:B) => 1) f) ->
          (forall f x, lib (F f x) (fun _: B => a * 1) == 
                         nuF (fun (x:A) (y:B) => a * 1) (fun y => lib (f y) (fun _: B => a * 1)) x)
          -> ~ 0==a -> fle (fmult a f) (pterm F F_mon) -> fle f (pterm F F_mon).
red; intros a f H nuF_eq_a H0 H1 x; apply Umult_le_simpl_left with a; trivial.
unfold pterm; rewrite <- (mu_stable_mult (Mfix F F_mon x) a (f_one B)).
apply muF_pterm_le_inv with (q:=fun (x:A) (y:B) => a * 1) (f:=fmult a f) (x:=x); intros;auto.
rewrite (muF_mult a (fun (x:A) (y:B) => 1) f); auto.
Qed.

Lemma muF_pterm_le_inv_mult : 
          forall q a f, fle f (muF q f) ->
          (forall f x, lib (F f x) (q x) == nuF q (fun y => lib (f y) (q y)) x) ->
          (forall f x, lib (F f x) (fun _: B => a * 1) == 
                         nuF (fun (x:A) (y:B) => a * 1) (fun y => lib (f y) (fun _: B => a * 1)) x) ->
          ~ 0==a ->
          fle (fmult a f) (pterm F F_mon) -> forall x, f x <= mu (Mfix F F_mon x) (q x).
intros; apply muF_pterm_le_inv; auto.
apply muF_pterm_le_mult with (a:=a); auto.
apply fle_trans with (muF q f); auto.
Qed.

(** ** Termination *)
Section Termination.

Variable next : A -> Ndistr A.

Definition Facc (t:A->U) := fun (x:A) => nu (next x) t.

Lemma Facc_monotonic : Fmonotonic Facc.
repeat red; unfold Facc; intros.
apply (nu_monotonic (next x)); auto.
Qed.
Hint Resolve Facc_monotonic.

Lemma Facc_continuous : Fcontlub Facc.
repeat red; unfold Facc; intros.
apply (nu_continuous (next x) (fn:=fn)); auto.
Qed.
Hint Resolve Facc_continuous.

Definition acc := mufix Facc.

Lemma acc_sup : forall x, nu (next x) acc  <= acc x.
intros; change (Facc acc x <= acc x).
unfold acc; apply mufix_sup; auto.
Qed.

Lemma prob_acc : forall f : A -> U,
        (forall x, nu (next x) f <= f x) -> fle acc f.
intros f H; unfold acc.
apply mufix_inv; auto.
Qed.

Lemma distr_acc : forall (f : A -> distr B) (q:A -> B -> U),
  okfun (fun x => nu (next x)  (fun y => mu (f y) (q y))) f q -> okfun acc f q.
unfold okfun,ok; intros.
apply prob_acc with (f:= fun y : A => mu (f y) (q y)); auto.
Qed.


(** ** Results on termination *)
Section Wfterm.

Variable R : A -> A -> Prop.
Hypothesis term_next : forall x, 1<= nu (next x) (f_one A).

(** *** First result *)
(** The distribution (next x) always gives values such that (R x y) **)
Section Result1.
Hypothesis support_next : 
   forall x f g, (forall y, R y x -> f y <= g y) -> nu (next x) f <= nu (next x) g.

Lemma acc_next_term : forall x,  Acc R x -> 1 <= acc x.
induction 1; intros.
apply Ule_trans with (nu (next x) acc).
apply Ule_trans with (1:= term_next x); auto.
apply acc_sup; auto.
Qed.

Lemma wf_next_term : (well_founded R) -> forall x, 1 <= acc x.
intros; apply acc_next_term; auto.
Qed.
End Result1.

(** *** Second result *)
(** The probability (next x) gives values such that (R x y) is greater than 1 **)

Hypothesis Rdec : forall x, dec (fun y => R y x).
Lemma acc_almost_term : 
   forall x, Acc R x -> (forall x, 1 <= nu (next x) (carac (Rdec x))) -> 1 <= acc x.
intros; apply acc_next_term; intros; auto.
setoid_replace (nu (next x0) f) with (nu (next x0) (fesp (carac (Rdec x0)) f)).
setoid_replace (nu (next x0) g) with (nu (next x0) (fesp (carac (Rdec x0)) g)).
apply (nu_monotonic (next x0)); red; auto.
unfold fesp; intros; apply carac_esp_fun_le; auto.
apply (Ndistr_eq_esp (next x0)); auto.
apply (Ndistr_eq_esp (next x0)); auto.
Qed.

Lemma wf_almost_term : 
   (well_founded R) -> (forall x, 1 <= nu (next x) (carac (Rdec x))) -> forall x, 1 <= acc x.
intros; apply acc_almost_term; auto.
Qed.

End Wfterm.
End Termination.

End Fixrules.
End Programs.
Hint Resolve lib_unit lib_let lib_if.

End Liberal.
