(** * Choice.v: An example of probabilistic choice *)
Require Export Prog.
Set Implicit Arguments.
Module Choice (Univ:Universe).
Module RP := (Rules Univ).
(* begin hide *)
Import Univ.
Import RP.
Import RP.PP.
Import RP.PP.MP.
Import RP.PP.MP.UP.
(* end hide *)
(** ** Definition of a probabilistic choice
We interpret the probabilistic program $p$ which executes 
two probabilistic programs $p_1$ and $p_2$ and then make a choice 
between the two computed results.
<<
let rec p () = let x = p1 () in let y = p2 () in choice x y 
>>*)
Section CHOICE.
Variable A : Type.
Variables p1 p2 : distr A.
Variable choice : A -> A -> A.
Definition p : distr A := Mlet p1 (fun x => Mlet p2 (fun y => Munit (choice x y))).
(** ** Main result 
 We estimate the probability for $p$ to satisfy $Q$ given estimations for 
both $p_1$ and $p_2$. *)
(** *** Assumptions 
We need extra properties on $p_1$, $p_2$ and $choice$.
- $p_1$ and $p_2$ terminate with probability $1$
- $Q$ value on $choice$ is not less than the sum of values of $Q$ on separate elements. 
If $Q$ is a boolean function it means than if one of $x$ or $y$ satisfies $Q$ 
then $(choice~x~y)$ will also satisfy $Q$ *)
Hypothesis p1_terminates : (mu p1 (f_one A))==1.
Hypothesis p2_terminates : (mu p2 (f_one A))==1.

Variable Q : A -> U. 
Hypothesis choiceok : forall x y, Q x + Q y <= Q (choice x y).

(** *** Proof of estimation
$\bfrac{\ok{k_1}{p_1}{Q}~~~\ok{k_2}{p_2}{Q}}
	  {\ok{k_1(1-k_2)+k_2}{p}{Q}}$
*)

Lemma choicerule : forall k1 k2,  
  k1 <= mu p1 Q -> k2 <= mu p2 Q ->  (k1 * ([1-] k2) + k2) <= mu p Q.
unfold p,Mlet,star; simpl; unfold unit; intros.
apply Ule_trans with 
  (mu p1 (fun x : A => mu p2 (fun y : A => Q x * ([1-] (Q y)) + Q y))).
apply Ule_trans with 
  (mu p1 (fun x : A => 
           ((mu p2 (fun y : A => Q x * ([1-] (Q y))))
           +(mu p2 Q)))).
change 
 (k1 * [1-] k2 + k2 <=
  mu p1 (fplus (fun x : A => mu p2 (fun y : A => Q x * [1-] (Q y)))
               (fun x => mu p2 Q))).
assert (H1 : fplusok (fun x : A => mu p2 (fun y : A => Q x * [1-] (Q y)))
               (fun x => mu p2 Q)).
repeat red; unfold finv; intros.
apply Ule_trans with (mu p2 (fun y : A => [1-] (Q y))).
apply (mu_monotonic p2); auto.
apply (mu_stable_inv p2 Q).
setoid_rewrite (mu_stable_plus p1 H1).
setoid_replace (mu p1 (fun _ : A => mu p2 Q)) 
  with (mu p2 Q); auto.
apply Ule_trans with 
   (k1 * [1-] (mu p2 Q) + (mu p2 Q)); auto.
apply Uplus_le_compat_left.
apply Ule_trans with 
(mu p1 (fun x : A => (Q x) * mu p2 (finv Q))).
apply Ule_trans with 
      ((mu p1 Q) * (mu p2 (finv Q))).
setoid_rewrite (mu_one_inv p2 p2_terminates Q); auto.
setoid_rewrite (mu_stable_mult_right p1 (mu p2 (finv Q)) Q); auto.
apply (mu_monotonic p1); red; intros.
setoid_rewrite <- (mu_stable_mult p2 (Q x) (finv Q)); auto.
exact (mu_cte_eq p1 (mu p2 Q) p1_terminates).

apply (mu_monotonic p1); red; intros.
assert (fplusok (fun y : A => Q x * [1-] (Q y)) Q).
repeat red; unfold finv; auto.
setoid_rewrite <- (mu_stable_plus p2 H1); auto.
apply (mu_monotonic p1); red; intros.
apply (mu_monotonic p2); red; intros.
apply Ule_trans with ((Q x) + (Q x0)); auto.
Qed.

End CHOICE.
End Choice.
