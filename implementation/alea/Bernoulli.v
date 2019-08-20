(** * Bernoulli.v: Simulating Bernoulli and Binomial distributions *)
Require Export Prog.
Require Export Prelude.
Set Implicit Arguments.

Module Bernoulli (Univ:Universe).
Module RP := (Rules Univ).
(* begin hide *)
Import Univ.
Import RP.
Import RP.PP.
Import RP.PP.MP.
Import RP.PP.MP.UP.
(* end hide *)

(** ** Program for computing a Bernoulli distribution
       bernoulli p gives true with probability p 
       and false with probability (1-p)
<<
let rec bernoulli x = if flip then 
        if x < 1/2 then false else bernoulli (2 p - 1)
        else if x < 1/2 then bernoulli (2 p) else true
>>*)
Hypothesis dec_demi : forall x : U, {x < [1/2]}+{[1/2] <= x}. 

Definition Fbern (f: U -> distr bool) (p:U) := 
    Mif Flip 
       (if dec_demi p then Munit false else f (p & p))
       (if dec_demi p then f (p + p) else Munit true).

Lemma Fbern_mon : forall f g : U -> distr bool, 
 (forall n, le_distr (f n) (g n)) -> forall n, le_distr (Fbern f n) (Fbern g n).
unfold Fbern; intros.
apply Mif_mon; case (dec_demi n); auto.
Qed.

Definition bernoulli : U -> distr bool := Mfix Fbern Fbern_mon.

(** ** Properties of the Bernoulli program *)

(** *** Proofs using fixpoint rules *)

Definition Mubern (q: bool -> U) (bern : U -> U) (p:U) := 
                if dec_demi p then [1/2]*(q false)+[1/2]*(bern (p+p))
                                      else  [1/2]*(bern (p&p)) + [1/2]*(q true).

Lemma Mubern_eq : forall (q: bool -> U) (f:U -> distr bool) (p:U),
             mu (Fbern f p) q  == Mubern q (fun y => mu (f y) q) p.
intros; unfold Fbern,Mubern; intros.
case (dec_demi p).
rewrite Mif_eq; rewrite Flip_ctrue; rewrite Flip_cfalse; rewrite Munit_eq; auto.
rewrite Mif_eq; rewrite Flip_ctrue; rewrite Flip_cfalse; rewrite Munit_eq; auto.
Qed.

   

Lemma Mubern_mon : forall (q: bool -> U), Fmonotonic (Mubern q).
red; red; intros; unfold Mubern; auto.
case (dec_demi x); repeat Usimpl; auto.
Qed.
Hint Resolve Mubern_mon Mubern_eq.

Lemma Bern_eq : 
    forall q : bool -> U, forall p, mu (bernoulli p) q == mufix (Mubern q) p.
intros; apply Ueq_sym.
unfold bernoulli; apply mufix_mu with (muF:=(Mubern q)) (q:=fun (p:U) => q); auto. 
Qed.
Hint Resolve Bern_eq.

Lemma Bern_commute : forall q : bool -> U, 
   mu_muF_commute_le Fbern Fbern_mon (fun (x:U)=>q) (Mubern q).
red; auto.
Qed.
Hint Resolve Bern_commute.

Lemma Bern_term : forall p, mu (bernoulli p) (f_one bool) == 1.
intros; apply Ueq_trans with (mufix (Mubern (f_one bool)) p); auto.
apply Ueq_trans with (lub U1min); auto.
unfold mufix; apply lub_eq_stable.
intro n; generalize p; induction n; simpl; auto.
intros; rewrite U1min_S.
unfold Mubern at 1; simpl.
unfold f_one; repeat Usimpl.
case (dec_demi p0); rewrite IHn; repeat Usimpl; auto.
Qed.
Hint Resolve Bern_term.

(** *** p is an invariant of Mubern qtrue *)

Lemma MuBern_true : forall p, Mubern B2U (fun q => q) p == p.
intros; unfold Mubern, B2U; case (dec_demi p); intros; repeat Usimpl.
apply half_twice; auto.
apply half_esp; auto.
Qed.
Hint Resolve MuBern_true.

Lemma MuBern_false : forall p, Mubern (finv B2U) (finv (fun q => q)) p == [1-]p.
intros; unfold Mubern, finv, B2U; case (dec_demi p); intros; repeat Usimpl.
rewrite Uplus_sym; rewrite Uinv_half; repeat Usimpl.
apply half_twice; auto.
rewrite Uinv_esp_plus.
apply half_twice; auto.
Qed.
Hint Resolve MuBern_false.


Lemma Bern_true : forall p, mu (bernoulli p) B2U == p.
intros; unfold bernoulli.
apply muF_eq with 
    (muFqinv:= Mubern (qinv (fun (x:U) => B2U) p))
    (muFq:=Mubern B2U)
    (q:=fun (x:U) => B2U)
    (f:=fun (x:U) => x);intros; auto.
unfold qinv; auto.
exact (Bern_term p).
Qed.

Lemma Bern_false : forall p, mu (bernoulli p) NB2U == [1-]p.
intros; apply Ueq_trans with (mu (bernoulli p) (finv B2U)).
apply mu_stable_eq; auto.
rewrite mu_inv_minus.
rewrite Bern_term; rewrite Bern_true; auto.
Qed.

Lemma Mubern_inv : forall (q: bool -> U) (f:U -> U) (p:U),
      Mubern (finv q) (finv f) p == [1-] Mubern q f p.
intros; unfold Mubern,finv.
case (dec_demi p); intro; auto.
Qed.
 
(** *** Proofs using lubs *)
(**   Invariant [pmin p]  $pmin(p)(n) = p - \frac{1}{2^n}$ *)

(** Property : $\forall p, \ok{p}{\mathrm{bernoulli}~p}{\mathbf{result}=\mathrm{true}}$ *)

Definition qtrue (p:U) := B2U.
Definition qfalse (p:U) := NB2U.

Lemma bernoulli_true :   okfun (fun p => p) bernoulli qtrue.
unfold bernoulli; intros.
apply okfun_le_compat with (fun p => lub (pmin p)) qtrue; auto.
apply fixrule with (p:= fun p => (pmin p)); auto; intros.
red; simpl; intros.
unfold Fbern.
red.
setoid_rewrite 
 (Mif_eq Flip 
   (if dec_demi x then Munit false else f (x & x))
   (if dec_demi x then f (x + x) else Munit true) (qtrue x)); simpl.
case (dec_demi x); simpl; intros.
(* Case x < 1/2 *)
unfold flip, unit, ctrue, cfalse; simpl.
repeat Usimpl.
apply Ule_trans with ((pmin (x + x) i) * [1/2]).
assert (x<= [1/2]); auto.
setoid_rewrite (pmin_plus_eq i H0).
Usimpl; trivial.
Usimpl; apply (H (x+x)); auto.
(* Case 1/2 <= x *)
unfold flip, unit, ctrue, cfalse; simpl.
repeat Usimpl.
apply Ule_trans with ((pmin (x & x) i) * [1/2] + [1/2]).
apply Ule_trans with (1:=(pmin_esp_le x i)); auto.
repeat Usimpl; apply (H (x&x)); auto.
Qed.

(** Property : $\forall p, \ok{1-p}{\mathrm{bernoulli}~p}{\mathbf{result}=\mathrm{false}} $ *)

Lemma bernoulli_false :  okfun (fun p => [1-] p) bernoulli qfalse.
unfold bernoulli; intros.
apply okfun_le_compat with (fun p => lub (pmin ([1-] p))) qfalse; auto.
apply fixrule with (p:= fun p => pmin ([1-] p)); auto; intros.
red; simpl; intros.
unfold Fbern.
red.
setoid_rewrite 
 (Mif_eq Flip 
   (if dec_demi x then Munit false else f (x & x))
   (if dec_demi x then f (x + x) else Munit true) (qfalse x)); simpl.
case (dec_demi x); simpl; intros.
(* Case x < 1/2 *)
unfold flip, unit, ctrue, cfalse; simpl.
repeat Usimpl.
apply Ule_trans with ([1/2] + (pmin ([1-] (x + x)) i) * [1/2]).
apply Ule_trans with (1:=pmin_esp_le ([1-] x) i).
setoid_rewrite (Uinv_plus_esp x x).
Usimpl; auto.
repeat Usimpl; apply (H (x+x)); auto.
(* Case 1/2 <= x *)
unfold flip, unit, ctrue, cfalse; simpl.
repeat Usimpl.
apply Ule_trans with ((pmin ([1-] (x & x)) i) * [1/2]).
setoid_rewrite (Uinv_esp_plus x x).
assert ([1-] x <= [1/2]); auto.
setoid_rewrite (pmin_plus_eq i H0).
repeat Usimpl; trivial.
repeat Usimpl; apply (H (x&x)); auto.
Qed.

(** Probability for the result of $(\mathrm{bernoulli}~p)$ to be true is exactly $p$ *)

Lemma qtrue_qfalse_inv : forall (b:bool) (x:U), qtrue x b == [1-] (qfalse x b).
intros; case b; simpl; auto.
Qed.

Lemma bernoulli_eq_true :  forall p, mu (bernoulli p) (qtrue p) == p.
intros; apply Ule_antisym.
apply Ule_trans with (mu (bernoulli p) (fun b => [1-] (qfalse p b))).
apply (mu_monotonic (bernoulli p)).
repeat red; intros.
setoid_rewrite (qtrue_qfalse_inv x); auto.
apply Ule_trans with ([1-] (mu (bernoulli p) (qfalse p))).
exact (mu_stable_inv (bernoulli p) (qfalse p)).
apply Uinv_le_perm_left.
apply (bernoulli_false p).
apply (bernoulli_true p).
Qed.

Lemma bernoulli_eq_false :  forall p, mu (bernoulli p) (qfalse p)== [1-]p.
intros; apply Ule_antisym.
apply Ule_trans with (mu (bernoulli p) (fun b => [1-] (qtrue p b))).
apply (mu_monotonic (bernoulli p)).
repeat red; intros.
setoid_rewrite (qtrue_qfalse_inv x p); auto.
apply Ule_trans with ([1-] (mu (bernoulli p) (qtrue p))).
exact (mu_stable_inv (bernoulli p) (qtrue p)).
apply Uinv_le_perm_left; Usimpl.
apply (bernoulli_true p).
apply (bernoulli_false p).
Qed.

Lemma bernoulli_eq :  forall p f, mu (bernoulli p) f == p * f true + ([1-]p) * f false.
intros; apply Ueq_trans with (mu (bernoulli p) (fun b => f true * qtrue p b + f false * qfalse p b)).
apply mu_stable_eq.
unfold feq,qtrue,qfalse,B2U,NB2U.
destruct x; repeat Usimpl; auto.
rewrite (mu_stable_plus (bernoulli p) (f:=fun b => f true * qtrue p b) 
                                                          (g:=fun b => f false * qfalse p b)).
rewrite (mu_stable_mult (bernoulli p) (f true) (qtrue p)).
rewrite (mu_stable_mult (bernoulli p) (f false) (qfalse p)).
rewrite bernoulli_eq_true; rewrite bernoulli_eq_false.
apply Uplus_eq_compat; auto.
repeat red; unfold fle,finv,qtrue,qfalse,B2U,NB2U; destruct x; repeat Usimpl; auto.
Qed.

Lemma bernoulli_total : forall p , mu (bernoulli p) (f_one bool)==1.
intros; rewrite bernoulli_eq; unfold f_one; repeat Usimpl; auto.
Qed.

(** ** Binomial distribution *)

(**  $ (\mathrm{binomial}~p~n)$  gives $k$ with probability $C_k^n p^k(1-p)^{n-k}$ *)

(** *** Definition and properties of binomial coefficients *)
Fixpoint comb (k n:nat) {struct n} : nat := 
         match n with O => match k with O => (1%nat) | (S l) => O end
                | (S m) => match k with O => (1%nat)
                                                    | (S l) => ((comb l m) + (comb k m))%nat end
         end.

Lemma comb_0_n : forall n, comb 0 n = 1%nat.
destruct n; trivial.
Qed.

Lemma comb_not_le : forall n k, le (S n) k -> comb k n=0%nat.
induction n; destruct k; simpl; auto with zarith; intros.
rewrite (IHn k); auto with zarith.
rewrite (IHn (S k)); auto with zarith.
Qed.

Lemma comb_Sn_n : forall n, comb (S n) n =0%nat.
intro; apply comb_not_le; auto.
Qed.

Lemma comb_n_n : forall n, comb n n = (1%nat).
induction n; simpl; auto.
rewrite comb_Sn_n; auto with zarith.
Qed.

Lemma comb_1_Sn : forall n, comb 1 (S n) = (S n).
induction n; auto.
replace (comb 1 (S (S n))) with ((comb 0 (S n)+comb 1 (S n))%nat); auto.
Qed.

Lemma comb_inv : forall n k, (k<=n)%nat -> comb k n = comb (n-k) n.
induction n; destruct k; simpl; auto with zarith; intros.
rewrite comb_Sn_n; rewrite comb_n_n; auto.
assert (Hle : (k<=n)%nat); auto with zarith.
case (le_lt_or_eq k n Hle); intros.
assert (Heq:(n-k)%nat=(S (n-(S k)))); auto with zarith.
pattern ((n-k)%nat) at 1; rewrite Heq.
rewrite (IHn (S k)); auto.
rewrite (IHn k); auto with zarith.
subst.
rewrite comb_Sn_n; rewrite comb_n_n; rewrite <- minus_n_n; trivial.
Qed.

Lemma comb_n_Sn : forall n, comb n (S n) = (S n).
intros; transitivity (comb (S n - n) (S n)).
apply comb_inv; auto.
rewrite <- minus_Sn_m; auto.
rewrite <- minus_n_n.
apply comb_1_Sn.
Qed.

Definition fc (p:U)(n k:nat) :=  (comb k n) */ (p^k * ([1-]p)^(n-k)).

Lemma fcp_0 : forall p n, fc p n O == ([1-]p)^n.
intros; unfold fc; rewrite comb_0_n; repeat Usimpl.
rewrite <- minus_n_O; auto.
Qed.

Lemma fcp_n : forall p n, fc p n n == p^n.
intros; unfold fc; rewrite comb_n_n; repeat Usimpl.
rewrite <- minus_n_n; auto.
Qed.

Lemma fcp_not_le : forall p n k, (S n <= k)%nat -> fc p n k == 0.
unfold fc; intros; rewrite comb_not_le; auto.
Qed.

Lemma fc0 : forall n k, fc 0 n (S k) == 0.
intros; unfold fc; simpl; repeat Usimpl; auto.
Qed.
Hint Resolve fc0.

Add Morphism fc with signature Ueq ==> eq ==> eq ==> Ueq as fc_eq_compat.
unfold fc; intros; rewrite H; auto.
Qed.

Hint Resolve fc_eq_compat.

Lemma sigma_fc0 : forall n k,  sigma (fc 0 n) (S k) ==1.
intros; rewrite sigma_S_lift.
rewrite fcp_0; rewrite sigma_zero; repeat Usimpl; auto.
Qed.
 
Lemma retract_class : forall f n, class (retract f n).
unfold retract; red; intros.
apply Ule_class; red; intros.
apply H; intro; auto.
Qed.
Hint Resolve retract_class.

Lemma fc_retract : 
     forall p n, ([1-]p^n == sigma (fc p n) n) -> retract (fc p n) (S n).
intros; apply (Ueq_orc p 0); intros; auto.
red; intros.
destruct k; simpl.
rewrite sigma_0; repeat Usimpl; auto.
apply Ule_trans with 0; auto.
rewrite H0; auto.
apply retractS_intro; auto.
apply retract_lt.
apply Ule_lt_trans with ([1-]p^n); auto.
apply Ule_trans with (p^n); auto.
rewrite fcp_n; auto.
Qed.
Hint Resolve fc_retract.

Lemma fc_Nmult_def : 
     forall p n k, ([1-]p^n == sigma (fc p n) n) -> Nmult_def (comb k n) (p^k * ([1-]p) ^(n-k)).
intros p n k Heq; destruct k.
rewrite comb_0_n; auto.
apply (Ueq_orc p 0); intros; auto.
(* case p == 0 *)
rewrite H; simpl; repeat Usimpl; auto.
(* case p <> 0 *)
assert (Hk:(S k < n \/n=S k\/ n < S k)%nat); try omega.
decompose sum Hk; clear Hk; intros.
(* S k < n *)
apply Nmult_def_lt.
apply Ule_lt_trans with (sigma (fc p n) n).
apply sigma_le with (k:=S k) (f:=fc p n); auto.
apply Ule_lt_trans with ([1-](p^n)); auto.
(* n=S k *)
subst.
rewrite comb_n_n; auto.
rewrite comb_not_le; auto with arith.
Qed.
Hint Resolve fc_Nmult_def.

Lemma fcp_S : 
    forall p n k, ([1-]p^n == sigma (fc p n) n) -> fc p (S n) (S k) == p * (fc p n k) + ([1-]p) * (fc p n (S k)).
intros;
assert (Hcase : (k<n \/ n=k \/ (S n)<=k)%nat); try omega. 
decompose sum Hcase.
unfold fc; simpl.
rewrite plus_Nmult_distr.
rewrite <- Umult_assoc.
rewrite Nmult_Umult_assoc_right; auto.
repeat Usimpl.
rewrite <- Nmult_Umult_assoc_right; auto.
apply Nmult_eq_compat; trivial.
repeat rewrite  Umult_assoc.
rewrite (Umult_sym ([1-]p) p).
rewrite <-  (Umult_assoc p ([1-]p)).
rewrite (Umult_sym ([1-]p) (p^k)); auto.
repeat rewrite  <- Umult_assoc; auto.
replace (n-k)%nat with (S (n-S k)); auto; omega.
exact (fc_Nmult_def p n (S k) H).
subst; repeat rewrite fcp_n.
rewrite fcp_not_le; repeat Usimpl; auto.
repeat (rewrite fcp_not_le; auto with arith).
repeat Usimpl; auto.
Qed.

Lemma sigma_fc_1 : forall p n, ([1-]p^n == sigma (fc p n) n) ->1==sigma (fc p n) (S n).
intros; rewrite sigma_S.
rewrite <- H; rewrite fcp_n; auto.
Qed.
Hint Resolve sigma_fc_1.

Lemma Uinv_exp : forall p n,  [1-](p^n)==sigma (fc p n) n.
induction n; auto.
(* case S n *)
apply (Ueq_orc p 0); intros; auto.
(* case p == 0 *)
rewrite sigma_S_lift.
rewrite fcp_0; rewrite sigma_zero; intros;
rewrite H; simpl; repeat Usimpl; auto.
(* case p <> 0 *)
assert (Hr:retract (fc p n) (S n)); auto.
(* main property *)
rewrite sigma_S_lift.
rewrite fcp_0.
apply Ueq_trans with (([1-] p) ^ S n + sigma (fun k : nat => p * fc p n k + ([1-]p) * fc p n (S k)) n).
rewrite (sigma_plus (fun k => p * fc p n k) (fun k => [1-] p * fc p n (S k))).
rewrite sigma_mult; auto.
rewrite <-IHn.
apply Ueq_trans with (p * [1-] p ^ n + (([1-] p) ^ S n + sigma (fun k : nat => [1-] p * fc p n (S k)) n));auto.
apply Ueq_trans with (p * [1-] p ^ n + (sigma (fun k : nat => [1-] p * fc p n k) (S n))).
rewrite sigma_mult; auto.
rewrite <- sigma_fc_1;auto; repeat Usimpl;apply Uexp_inv_S.
rewrite sigma_S_lift; repeat Usimpl; rewrite fcp_0; auto.
repeat Usimpl.
apply sigma_eq_compat; intros.
apply Ueq_sym; apply fcp_S; auto.
Qed.

Hint Resolve Uinv_exp.

Lemma Nmult_comb : forall p n k, Nmult_def (comb k n) (p ^ k * ([1-] p) ^ (n - k)).
auto.
Qed.
Hint Resolve Nmult_comb.

Definition qk (k n:nat) : U := if eq_nat_dec k n then 1 else 0.

(** *** Definition of binomial distribution *)
Fixpoint binomial (p:U)(n:nat) {struct n}: distr nat := 
    match n with O => (Munit O)
                     | S m => Mlet (binomial p m) 
                                     (fun x => Mif (bernoulli p) (Munit (S x)) (Munit x))
    end.

(** *** Properties of binomial distribution *)
Lemma binomial_eq_k : 
   forall p n k, mu (binomial p n) (qk k) == fc p n k.
induction n; intros.
(* case n = 0 *)
simpl; destruct k; unfold unit,qk; auto.
rewrite fcp_0; auto.
(* cas n<>0 *)
simpl binomial.
simpl mu.
apply Ueq_trans with 
(star (mu (binomial p n))
  (fun x : nat =>
   star (mu (bernoulli p))
     (fun x0 : bool => mu (if x0 then Munit (S x) else Munit x))) (qk k));
auto.
unfold star.
apply Ueq_trans with 
 (mu (binomial p n)
  (fun x : nat => p * (qk k (S x)) + ([1-]p) * (qk k x))).
apply mu_stable_eq; red; intros.
rewrite bernoulli_eq; unfold Munit; simpl; auto.
destruct k.
(* case k = 0 *)
apply Ueq_trans with (mu (binomial p n) (fun x => [1-] p * qk 0 x)).
apply mu_stable_eq; red; unfold qk at 1; intros.
rewrite if_else; auto; repeat Usimpl; auto.
rewrite (mu_stable_mult (binomial p n) ([1-]p) (qk 0)).
rewrite IHn; simpl; repeat Usimpl; auto.
repeat rewrite fcp_0; auto.
(* Case S k *)
apply Ueq_trans with  (mu (binomial p n) (fun x : nat => p * qk k x + [1-] p * qk (S k) x)).
apply mu_stable_eq; red; intro; repeat Usimpl.
unfold qk; intros.
case (eq_nat_dec k x); intro.
rewrite if_then; auto.
rewrite if_else; auto.
rewrite (mu_stable_plus (binomial p n) (f:=fun x : nat => p * qk k x) (g:=fun x : nat => [1-] p * qk (S k) x)).
(* *)
rewrite (mu_stable_mult (binomial p n) p (qk k)).
rewrite (mu_stable_mult (binomial p n) ([1-]p) (qk (S k))).
rewrite IHn.
rewrite IHn.
rewrite fcp_S; auto.
(* fplusok *)
repeat red; unfold finv,qk; intros.
case (eq_nat_dec k x); intro; auto.
Qed.

End Bernoulli.
