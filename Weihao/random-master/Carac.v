(** * Carac.v: Characteristic functions *)
Require Export Prog.
Set Implicit Arguments.
Unset Standard Proposition Elimination Names.
Require Export Sets.
Require Export Arith.
Module CaracFun (Univ:Universe).

Module RP := (Rules Univ).
(* begin hide *)
Import Univ.
Import RP.
Import RP.PP.
Import RP.PP.MP.
Import RP.PP.MP.UP.
(* end hide *)


Definition carac (A:Type)(P:A -> Prop)(Pdec:dec P)(z:A): U := if (Pdec z) then 1 else 0.

Lemma carac_one : forall (A:Type)(P:A -> Prop)(Pdec:dec P)(z:A),
       P z -> carac Pdec z == 1.
unfold carac; intros; case (Pdec z); intuition.
Qed.

Lemma carac_zero : forall (A:Type)(P:A -> Prop)(Pdec:dec P)(z:A),
       ~P z -> carac Pdec z == 0.
unfold carac; intros; case (Pdec z); intuition.
Qed.

Lemma carac_unit : forall (A:Type)(P:A -> Prop)(Pdec : dec P)(a:A),
                                  (P a) -> 1 <= (mu (Munit a)) (carac Pdec).
simpl;intros.
unfold unit,carac.
case (Pdec a); intuition.
Qed.

Lemma carac_let_one : forall (A B:Type)(m1: distr A)(m2: A -> distr B) (P:B -> Prop)(Pdec: dec P),
     mu m1 (f_one A) == 1 -> (forall x:A, 1 <= mu (m2 x) (carac Pdec)) -> 1 <= mu (Mlet m1 m2) (carac Pdec) .
intros A B m1 m2.
simpl.
unfold star; intuition.
rewrite <- H.
apply (mu_monotonic m1).
red; intros.
unfold f_one; simpl; auto.
Qed.

Lemma carac_let : forall (A B:Type)(m1: distr A)(m2: A->distr B) (P:A->Prop)(Pdec: dec P)(f:B->U)(p:U),
     1 <= mu m1 (carac Pdec) -> (forall x:A, P x -> p <= mu (m2 x) f)
     -> p <= mu (Mlet m1 m2) f.
intros A B m1 m2.
simpl.
unfold star; intuition.
setoid_replace p with (mu m1 (fun x => p * (carac Pdec x))); auto.
apply (mu_monotonic m1).
red; intros.
unfold carac at 1; destruct (Pdec x);repeat Usimpl; auto.
rewrite (mu_stable_mult m1 p (carac Pdec)).
apply Ueq_trans with (p * 1); auto.
Qed.

Lemma carac_incl: forall (A:Type)(P Q:A -> Prop)(Pdec: dec P)(Qdec: dec Q),
                                incl P Q -> fle (carac Pdec) (carac Qdec).
red; intros;unfold carac.
case (Pdec x); case (Qdec x); intuition.
absurd (Q x); intuition.
Qed.

Definition equiv_dec : forall (A:Type)(P Q:A -> Prop),dec P -> equiv P Q -> dec Q.
intros A P Q Pdec EQ.
unfold dec; intro a; case (Pdec a); intro.
left; assert (eqA:=EQ a); intuition.
right; assert (eqA:=EQ a); intuition.
Defined.

Lemma carac_equiv : forall (A:Type)(P Q:A -> Prop)(Pdec : dec P)(EQ : equiv P Q),
feq  (carac (equiv_dec Pdec EQ)) (carac Pdec).
red; unfold carac; intros; unfold equiv_dec; case (Pdec x); intuition.
Qed.

Definition union_dec : forall (A:Type)(P Q:A -> Prop), dec P -> dec Q -> dec (union P Q).
intros A P Q Pdec Qdec.
unfold dec,union; intro a; case (Pdec a); intuition; case (Qdec a); intuition.
Defined.

Lemma carac_union : forall (A:Type)(P Q:A -> Prop)(Pdec : dec P)(Qdec : dec Q),
feq  (carac (union_dec Pdec Qdec)) (fun a => (carac Pdec a) + (carac Qdec a)).
red; unfold carac; intros. 
unfold union_dec; case (Pdec x); intuition; case (Qdec x); intuition.
Qed.

Definition inter_dec : forall (A:Type)(P Q:A -> Prop),(dec P)->(dec Q) -> dec (inter P Q).
intros A P Q Pdec Qdec.
unfold dec,inter; intro a; case (Pdec a); intuition; case (Qdec a); intuition.
Defined.

Lemma carac_inter : forall (A:Type)(P Q:A -> Prop)(Pdec : dec P)(Qdec : dec Q),
feq  (carac (inter_dec Pdec Qdec)) (fun a => (carac Pdec a) * (carac Qdec a)).
red; unfold carac; intros. 
unfold inter_dec; case (Pdec x); intuition; case (Qdec x); intuition.
Qed.

Definition  compl_dec : forall (A:Type)(P:A -> Prop), dec P -> dec (compl P).
intros A P Pdec.
unfold dec,compl; intro a; case (Pdec a); intuition.
Defined.

Lemma carac_compl : forall (A:Type)(P:A -> Prop)(Pdec : dec P),
feq  (carac (compl_dec Pdec)) (fun a => [1-](carac Pdec a)).
red; unfold carac; intros. 
unfold compl_dec; case (Pdec x); intuition.
Qed.

Definition empty_dec : forall (A:Type)(P:A->Prop), equiv P (empty A) ->dec P.
unfold dec,empty; right; red; intros.
apply (equiv_empty_false (P:=P)) with x; auto.
Defined.

Lemma carac_empty : forall (A:Type)(P:A->Prop)
       (empP:equiv P (empty A)),feq (carac (empty_dec empP)) (f_zero A).
red; unfold carac; intros. 
unfold empty_dec; intuition.
Qed.

Lemma carac_mult_fun : forall (A:Type)(P:A -> Prop)(Pdec : dec P)(f g:A->U),
  (forall x, P x -> f x==g x) -> forall x, carac Pdec x * f x == carac Pdec x * g x.
unfold carac; intros; destruct (Pdec x); repeat Usimpl; auto.
Qed.

Lemma carac_esp_fun : forall (A:Type)(P:A -> Prop)(Pdec : dec P)(f g:A->U),
  (forall x, P x -> f x==g x) -> forall x, carac Pdec x & f x == carac Pdec x & g x.
unfold carac; intros; destruct (Pdec x); repeat Usimpl; auto.
Qed.
Hint Resolve carac_esp_fun.

Lemma carac_esp_fun_le : forall (A:Type)(P:A -> Prop)(Pdec : dec P)(f g:A->U),
  (forall x, P x -> f x<=g x) -> forall x, carac Pdec x & f x <= carac Pdec x & g x.
unfold carac; intros; destruct (Pdec x); repeat Usimpl; auto.
Qed.
Hint Resolve carac_esp_fun_le.

Lemma carac_ok : forall (A:Type)(P Q:A -> Prop)(Pdec : dec P)(Qdec : dec Q),
        (forall x, P x -> ~ Q x) -> fplusok (carac Pdec) (carac Qdec).
red; red; intros.
unfold finv; case (Pdec x); intro.
rewrite carac_one; auto; rewrite carac_zero; auto.
rewrite carac_zero; auto.
Qed.
Hint Resolve carac_ok.


(** ** Modular reasoning on programs *)

Lemma mu_carac_esp : forall (A:Type)(m:distr A)(P:A -> Prop)(Pdec : dec P)(f:A->U),
  1<=mu m (carac Pdec) -> mu m f == mu m (fun x => carac Pdec x & f x).
intros; apply Ule_antisym.
apply Ule_trans with (mu m (carac Pdec) & mu m f).
setoid_replace (mu m (carac Pdec)) with 1; auto.
apply mu_le_esp with (f:=carac Pdec) (g:=f).
apply mu_monotonic.
repeat red; intros; auto.
Qed.

Lemma mu_cut : forall (A:Type)(m:distr A)(P:A -> Prop)(Pdec : dec P)(f g:A->U),
  (forall x, P x -> f x==g x) -> 1<=mu m (carac Pdec) -> mu m f == mu m g.
intros; apply Ueq_trans with (mu m (fun x => carac Pdec x & f x)).
apply mu_carac_esp; auto.
intros; apply Ueq_trans with (mu m (fun x => carac Pdec x & g x)).
apply mu_stable_eq; repeat red; intros;auto.
apply Ueq_sym; apply mu_carac_esp; auto.
Qed.

(** count the number of elements between 0 and n-1 which satisfy P *)
Fixpoint nb_elts (P:nat -> Prop)(Pdec : dec P)(n:nat) {struct n} : nat :=
match n with
   0 => 0%nat
  | S n => if Pdec n then (S (nb_elts Pdec n)) else (nb_elts Pdec n)
end.

(** the probability for a random number between 0 and n to satisfy P is equal 
     to the number of elements below n which satisfy P divided by n+1 *)

Lemma random_carac : forall (P:nat -> Prop)(Pdec : dec P)(n:nat),
    random n (carac Pdec) == (nb_elts Pdec (S n)) */ [1/]1+n.
unfold random,fnth; intros.
elim (S n); simpl; intros;auto.
rewrite sigma_S.
rewrite H; unfold carac;case (Pdec n0); Usimpl; auto.
Qed.

Lemma mu_carac_inv : forall (A:Type)(P:A->Prop)(Pdec:dec P)(notPdec : dec (fun x => ~ (P x))) 
     (m : distr A), mu m (carac Pdec) == mu m (finv (carac notPdec)).
intros; apply (mu_stable_eq m); red; intros.
unfold finv,carac.
case (Pdec x); case (notPdec x); intuition.
Qed.


Section SigmaFinite.
Variable A:Type.
Variable decA : forall x y:A, {x=y}+{~x=y}.

Section RandomFinite.

(** ** Uniform measure on finite sets *)

(** *** Distribution for [random_fin P] over $\{k:nat | k \leq n\}$
The distribution associated to [random_fin P] is 
       $f \mapsto \Sigma_{a\in P} \frac{f(a)}{n+1}$
       with $n+1$ the size of $P$
       we cannot factorize $\frac{1}{n+1}$ because of possible overflow *)

Fixpoint sigma_fin (f:A->U)(P:A->Prop)(FP:finite P){struct FP}:U := 
match FP with
  | (fin_eq_empty eq) => 0
  | (fin_eq_add x Q nQx FQ eq) => (f x) + sigma_fin f FQ
end.


Definition retract_fin (P:A->Prop) (f:A->U) := 
     forall Q (FQ: finite Q), incl Q P -> forall x, ~(Q x) -> (P x) -> f x <= [1-](sigma_fin f FQ).

Lemma retract_fin_incl : forall P Q f, retract_fin P f -> incl Q P -> retract_fin Q f.
unfold retract_fin; intros.
apply (H Q0 FQ); auto.
apply incl_trans with Q; auto.
Qed.

Lemma sigma_fin_monotonic : forall (f g : A -> U)(P:A->Prop)(FP:finite P),
       (forall x, P x -> (f x)<=(g x))-> sigma_fin f FP <= sigma_fin g FP.
induction FP; simpl; intros; auto.
apply Ule_trans with (f x + sigma_fin g FP); repeat Usimpl.
apply IHFP.
intros; case (e x0); unfold add in *; intuition.
apply H; case (e x); unfold add in *; intuition.
Qed.

Lemma sigma_fin_eq_compat : 
forall (f g : A -> U)(P:A->Prop)(FP:finite P),
       (forall x, P x -> (f x)==(g x))-> sigma_fin f FP == sigma_fin g FP.
intros; apply Ule_antisym; apply sigma_fin_monotonic; auto.
intros; rewrite (H x); auto.
Qed.


Lemma retract_fin_le : forall (P:A->Prop) (f g:A->U), 
        (forall x, P x -> f x <= g x) -> retract_fin P g -> retract_fin P f.
unfold retract_fin; intros.
apply Ule_trans with (g x); auto.
apply Ule_trans with ([1-] sigma_fin g FQ); auto.
apply Uinv_le_compat.
apply sigma_fin_monotonic; auto.
Qed.

Lemma sigma_fin_mult : forall (f : A -> U) c (P:A->Prop)(FP:finite P),
       retract_fin P f -> sigma_fin (fun k  => c * f k) FP == c * sigma_fin f FP.
induction FP; simpl; intros.
repeat Usimpl; auto.
assert (incl Q P).
apply incl_trans with (add x Q); auto.
rewrite Udistr_plus_left; auto.
rewrite IHFP; auto.
apply retract_fin_incl with P; auto.
case (e x); intuition.
Qed.

Lemma sigma_fin_plus : forall (f g: A -> U) (P:A->Prop)(FP:finite P),
       sigma_fin (fun k  => f k + g k) FP == sigma_fin f FP + sigma_fin g FP.
induction FP; simpl; intros.
repeat Usimpl; auto.
rewrite IHFP.
repeat norm_assoc_left; repeat Usimpl.
repeat norm_assoc_right; repeat Usimpl; auto.
Qed.

Lemma sigma_fin_prod_maj : 
forall (f g : A -> U)(P:A->Prop)(FP:finite P),
       sigma_fin (fun k  => f k * g k) FP <= sigma_fin f FP.
induction FP; simpl; auto.
Qed.

Lemma sigma_fin_prod_le : 
forall (f g : A -> U) (c:U) , (forall k, f k <= c) -> forall (P:A->Prop)(FP:finite P),
retract_fin P g -> sigma_fin (fun k  => f k * g k) FP <= c * sigma_fin g FP.
induction FP; simpl; intros.
repeat Usimpl; auto.
assert (incl Q P).
apply incl_trans with (add x Q); auto.
assert (retract_fin Q g).
apply retract_fin_incl with P; auto.
apply Ule_trans with ((f x) * (g x) + (c * sigma_fin g FP)); auto.
apply Ule_trans with ( c * (g x) + (c * sigma_fin g FP)); auto.
rewrite Udistr_plus_left; auto.
case (e x); intuition.
Qed.

Lemma sigma_fin_prod_ge : 
forall (f g : A -> U) (c:U) , (forall k, c <= f k) -> forall (P:A->Prop)(FP:finite P),
retract_fin P g -> c * sigma_fin g FP <= sigma_fin (fun k  => f k * g k) FP.
induction FP; simpl; intros.
repeat Usimpl; auto.
assert (incl Q P).
apply incl_trans with (add x Q); auto.
assert (retract_fin Q g).
apply retract_fin_incl with P; auto.
apply Ule_trans with ((f x) * (g x) + (c * sigma_fin g FP)); auto.
apply Ule_trans with ( c * (g x) + (c * sigma_fin g FP)); auto.
case (e x); intuition.
Qed.
Hint Resolve sigma_fin_prod_maj sigma_fin_prod_ge sigma_fin_prod_le.

Lemma sigma_fin_inv : forall (f g : A -> U)(P:A->Prop)(FP:finite P),
       retract_fin P f ->
       [1-] sigma_fin (fun k  => f k * g k) FP ==
       sigma_fin (fun k => f k * [1-] g k) FP + [1-] sigma_fin f FP.
induction FP; simpl.
repeat Usimpl; auto.
intro.
assert (incl Q P).
apply incl_trans with (add x Q); auto.
assert (retract_fin Q f).
apply retract_fin_incl with P; auto.
assert (px:P x).
case (e x); intuition.

apply Uplus_eq_simpl_right with ((f x) * (g x)).
repeat Usimpl; auto.

apply Uinv_le_perm_right.
rewrite (Udistr_inv_left (f x) (g x)).
repeat norm_assoc_right; apply Uplus_le_compat_right.
apply Ule_trans with 
  (sigma_fin f FP + [1-] (f x + sigma_fin f FP)); repeat Usimpl.
apply (sigma_fin_prod_maj f (fun k => [1-](g k)) FP).

assert (sigma_fin f FP <= [1-] (f x)); auto.
rewrite <- (Uinv_plus_right H2); auto.

assert (sigma_fin (fun k => f k * g k) FP <= [1-] (f x * g x)).
apply Ule_trans with (sigma_fin f FP); auto.

apply Ule_trans with ([1-] (f x)); auto.
rewrite (Uinv_plus_left H2).
apply Ueq_trans with (1:=IHFP H1).
rewrite (Uplus_sym (f x * [1-] (g x))
                          (sigma_fin (fun k  => f k * [1-] (g k)) FP)).
repeat norm_assoc_right;apply Uplus_eq_compat_right.
setoid_rewrite (Uplus_sym  ([1-] (f x + sigma_fin f FP)) (f x * g x)).
repeat norm_assoc_left.
assert ([1-] (g x) <= [1-] (g x)); auto.

rewrite <- (Udistr_plus_left (f x) H3).
rewrite (Uinv_opp_left (g x)).
rewrite (Umult_one_right (f x)); auto.
rewrite (Uplus_sym (f x) ([1-] (f x + sigma_fin f FP))).
apply Ueq_sym; apply Uinv_plus_left; auto.
Qed.

Lemma sigma_fin_equiv : forall f P Q  (FP:finite P) (e:equiv P Q),
    (sigma_fin f (fin_equiv e FP)) = (sigma_fin f FP).
induction FP; simpl; intros; auto.
Qed.

Lemma sigma_fin_rem : forall f P (FP:finite P) a, 
             P a -> sigma_fin f FP == f a + sigma_fin f (finite_rem decA a FP).
induction FP;  intuition.
case (equiv_empty_false a e);auto.
simpl; case (decA x a); simpl; intros.
case e0; unfold eq_rect_r;simpl; auto.
rewrite sigma_fin_equiv; auto.
rewrite (IHFP a); auto.
case (e a); unfold add; intuition.
case f0; auto.
Qed.

Lemma sigma_fin_incl : forall f P (FP:finite P) Q (FQ:finite Q),
              (incl P Q) -> sigma_fin f FP <= sigma_fin f FQ.
induction FP; simpl; intros; auto.
destruct FQ; simpl; intros.
case incl_add_empty with (a:=x) (P:=Q).
apply incl_trans with Q0; auto.
apply incl_trans with P; auto.
case (decA x x0); intro.
(* case x=x0*)
subst; Usimpl; auto.
apply IHFP.
apply incl_trans with (rem x0 P); auto.
apply incl_add_rem; auto.
apply incl_trans with (rem x0 Q0); auto.
rewrite incl_rem_add_iff; auto.
(* Case x<>x0 *)
rewrite (sigma_fin_rem f FQ x); auto.
repeat norm_assoc_left.
rewrite (Uplus_sym (f x0) (f x)).
repeat norm_assoc_right.
Usimpl.
assert (H3:~(rem x Q1 x0)).
unfold rem; intuition.
assert (incl Q (add x0 (rem x Q1))).
red; intros; case (e0 x1); clear e0; intuition.
case (e x1); clear e; intuition.
generalize (H x1); clear H; intuition.
unfold add,rem in *; intuition.
subst; intuition.
case (decA x1 x0); intuition; subst; intuition.
case (decA x1 x); intuition; subst; intuition.
exact (IHFP (add x0 (rem x Q1)) (fin_eq_add H3 (finite_rem decA x FQ) (equiv_refl (add x0 (rem x Q1)))) H0).
assert (P x).
red in e; rewrite e; auto.
assert (Q0 x);auto.
assert (Q1 x);auto.
case (e0 x); intuition.
case H4; intuition.
Qed.

Lemma sigma_fin_unique : forall f P Q (FP:finite P) (FQ:finite Q), (equiv P Q) -> sigma_fin f FP == sigma_fin f FQ.
intros; apply Ule_antisym.
apply sigma_fin_incl; auto.
apply sigma_fin_incl; auto.
Qed.

Lemma sigma_fin_cte : forall c P (FP:finite P), 
       sigma_fin (fun _ => c) FP == (size FP) */ c.
induction FP; auto.
simpl sigma_fin; simpl size; rewrite IHFP; auto.
Qed.

(** *** Definition and Properties of [random_fin] *)

Variable P : A->Prop.
Variable FP : finite P.
Let s:= (size FP - 1)%nat.
Lemma pred_size_le : (size FP <=S s)%nat.
unfold s; omega.
Qed.
Hint Resolve pred_size_le.


Lemma pred_size_eq : notempty P -> size FP =S s.
destruct FP; intros; simpl.
unfold notempty in *; contradiction.
unfold s; simpl; omega.
Qed.

Definition random_fin :M A := fun (f:A->U) => sigma_fin (fun k => Unth s *  f k) FP.

Lemma fnth_retract_fin: 
       forall n, (size FP<=S n)%nat -> (retract_fin P (fun _ => [1/]1+n)).
red; intros.
rewrite sigma_fin_cte.
apply Ule_trans with ([1-] (n */ [1/]1+n)); auto.
apply Uinv_le_compat.
apply Nmult_le_compat_left.
apply le_trans with (size (finite_rem decA x FP)); auto.
apply size_incl; auto.
unfold incl, rem; intuition.
subst; intuition.
apply le_S_n.
apply le_trans with (size FP); auto.
rewrite (size_finite_rem decA x FP); auto.
Qed.

Lemma random_fin_stable_inv : stable_inv random_fin.
unfold random_fin, stable_inv, finv; intros; auto.
rewrite (@sigma_fin_inv (fun k => [1/]1+s) f P FP); auto.
apply fnth_retract_fin; trivial.
Qed.

Lemma random_fin_stable_plus : stable_plus random_fin.
unfold random_fin, stable_plus, fplus; intros; auto.
unfold fplusok, fle, finv in H.
apply Ueq_trans with 
 (sigma_fin (fun k => ([1/]1+s * f k) + ([1/]1+s  * g k)) FP).
apply sigma_fin_eq_compat; intros; auto.
apply sigma_fin_plus with (f:=fun k => Unth s * f k)
                      (g:=fun k => Unth s * g k); auto.
Qed.

Lemma random_fin_stable_mult : stable_mult random_fin.
unfold random_fin, stable_mult, fmult; intros; auto.
apply Ueq_trans with  (sigma_fin (fun l => k * ([1/]1+s * f l)) FP).
apply sigma_fin_eq_compat; intros; auto.
apply sigma_fin_mult with (f:=fun k  => Unth s * f k).
apply retract_fin_le with (fun (k:A) => [1/]1+s); auto.
apply fnth_retract_fin; auto.
Qed.

Lemma random_fin_monotonic : monotonic random_fin.
unfold monotonic, random_fin; intros.
red in H.
apply sigma_fin_monotonic; auto.
Qed.

Definition Random_fin : (distr A).
exists random_fin.
apply random_fin_stable_inv; trivial.
apply random_fin_stable_plus.
apply random_fin_stable_mult; trivial.
apply random_fin_monotonic.
Defined.

Lemma random_fin_total : notempty P -> mu Random_fin (f_one A) == 1.
intros; simpl; unfold random_fin.
unfold f_one.
apply Ueq_trans with  (sigma_fin (fun k =>  [1/]1+s) FP).
apply sigma_fin_eq_compat.
intros; repeat Usimpl; auto.
rewrite sigma_fin_cte.
rewrite pred_size_eq; auto.
Qed.
End RandomFinite.

Lemma random_fin_carac : 
    forall P Q (FP:finite P) (decQ:dec Q), 
         mu (Random_fin FP) (carac decQ) == size (finite_inter decQ FP) */ [1/]1+(size FP-1)%nat.
intros; simpl mu.
unfold random_fin.
pattern P at 1 3 4 5, FP at 2 3.
elim FP; intros; auto.
simpl sigma_fin.
unfold carac at 1.
rewrite H.
case (decQ x); intro.
rewrite size_inter_add_in; auto.
rewrite Nmult_S; auto.
repeat Usimpl; rewrite size_inter_add_notin; auto.
Qed.

Lemma random_fin_P : forall P (FP:finite P) (decP:dec P), 
         notempty P -> mu (Random_fin FP) (carac decP) ==1.
intros; rewrite random_fin_carac.
rewrite (size_inter_incl decA decP FP FP); auto.
pattern (size FP) at 1; rewrite pred_size_eq; auto.
Qed.


End SigmaFinite.
End CaracFun.

