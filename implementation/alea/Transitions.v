(** * Transitions.v: Probabilistic Deterministic Transition System *)


Require Export Prog.
Require Nelist.
Set Implicit Arguments.

Module PTS(Univ:Universe).
Module RP := (Rules Univ).
(* begin hide *)
Import Univ.
Import RP.
Import RP.PP.
Import RP.PP.MP.
Import RP.PP.MP.UP.
(* end hide *)
Section TRANSITIONS.

Variable A : Type.

(** ** One step of probabilistic transition *)

Variable step : A -> distr A.

(** ** Extension to distributions on sequences of length k *)
Export Nelist.

Definition add_step (start : distr (nelist A)) :  M (nelist A) := 
  fun f => mu start (fun l => (mu (step (hd l)) (fun x => (f (add x l))))).

Lemma add_step_stable_inv : forall (start : distr (nelist A)), stable_inv (add_step start).
red; unfold add_step; intros.
apply Ule_trans with 
(mu start (finv (fun l : nelist A => mu (step (hd l)) (fun x : A => f (add x l))))).
apply (mu_monotonic start).
repeat red; intros.
apply (mu_stable_inv (step (hd x))) with (f:= fun x0 : A => f (add x0 x)).
apply (mu_stable_inv start).
Qed.

Lemma add_step_stable_plus : forall (start : distr (nelist A)), stable_plus (add_step start).
red; unfold add_step; intros.
apply Ueq_trans with 
(mu start (fplus (fun l => (mu (step (hd l)) (fun x : A => f (add x l))))
                 (fun l => (mu (step (hd l)) (fun x : A => g (add x l)))))).
apply (mu_stable_eq start).
repeat red; intros.
apply (mu_stable_plus (step (hd x)))
 with (f:= fun x0 : A => f (add x0 x)) (g:= fun x0 : A => g (add x0 x)).
repeat red in H; repeat red; intros; unfold finv.
apply (H (add x0 x)).
apply (mu_stable_plus start).
repeat red in H; repeat red; intros; unfold finv.
apply Ule_trans with 
   (mu (step (hd x)) (finv (fun x0 : A => g (add x0 x)))).
apply (mu_monotonic (step (hd x))).
repeat red; intros; apply (H (add x0 x)).
apply (mu_stable_inv (step (hd x))).
Qed.


Lemma add_step_stable_mult : forall (start : distr (nelist A)), stable_mult (add_step start).
red; unfold add_step; intros.
apply Ueq_trans with 
(mu start (fmult k (fun l => (mu (step (hd l)) (fun x : A => f (add x l)))))).
apply (mu_stable_eq start).
repeat red; intros.
apply (mu_stable_mult (step (hd x)) k)
 with (f:= fun x0 : A => f (add x0 x)).
apply (mu_stable_mult start).
Qed.

Lemma add_step_monotonic : forall (start : distr (nelist A)), monotonic (add_step start).
red; unfold add_step; intros.
apply (mu_monotonic start).
repeat red; intros.
apply (mu_monotonic (step (hd x)))
 with (f:= fun x0 : A => f (add x0 x)).
repeat red; intros.
apply (H (add x0 x)).
Qed.

Definition Add_step : (distr (nelist A)) -> (distr (nelist A)).
intros start; exists (add_step start).
apply add_step_stable_inv.
apply add_step_stable_plus.
apply add_step_stable_mult.
apply add_step_monotonic.
Defined.


(** Definition of the measure *)
Fixpoint path (k:nat) (s : A) {struct k} : distr (nelist A) := 
   match k with 
      O => Munit (singl s) 
    |(S p) => Add_step (path p s)
   end.

(** The opposite view of composition starting from one step *)

Lemma path_unfold : forall k s f,
    mu (path (S k) s) f == mu (step s) (fun x => mu (path k x) (fun l => f (app l (singl s)))).
induction k; intros.
simpl; unfold unit; auto.
apply Ueq_trans with (add_step (path (S k) s) f); trivial.
unfold add_step.
setoid_rewrite 
   (IHk s (fun l => mu (step (hd l)) (fun x : A => f (add x l)))).
apply (mu_stable_eq (step s)).
red; intros.
pose (g:=fun l => f (app l (singl s))).
apply Ueq_trans with 
  (mu (path k x)
  (fun l : nelist A => mu (step (hd l)) (fun x0 : A => g (add x0 l)))); trivial.
apply (mu_stable_eq (path k x)); red; intros.
rewrite hd_app; auto.
Qed.

End TRANSITIONS.


End PTS.
