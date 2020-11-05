From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype path
  ssrint rat bigop.

From extructures Require Import ord fset fmap ffun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.

(* Consolidate this stuff in extructures. *)

Lemma filterm0 (T : ordType) (S : Type) (f : T -> S -> bool) : filterm f emptym = emptym.
Proof. by apply/eq_fmap=> x; rewrite filtermE. Qed.

Lemma filterm_set (T : ordType) (S : Type) (f : T -> S -> bool) m x y :
  filterm f (setm m x y) =
  if f x y then setm (filterm f m) x y
  else remm (filterm f m) x.
Proof.
apply/eq_fmap=> x'; have [yes|no] := boolP (f x y).
  by rewrite !(setmE, filtermE); case: eqP=> //= ->; rewrite yes.
by rewrite remmE !filtermE setmE; case: eqP no=> //= -> /negbTE ->.
Qed.

Lemma fsetUDr (T : ordType) (A B C : {fset T}) :
  A :|: B :\: C = (A :|: B) :\: (C :\: A).
Proof.
apply/eq_fset=> x; rewrite !(in_fsetU, in_fsetD).
by case: (x \in A).
Qed.

Lemma bigcupS (I : eqType) (T : ordType) (P : I -> bool) (F : I -> {fset T}) s X :
  reflect (forall i : I, i \in s -> P i -> fsubset (F i) X)
          (fsubset (\bigcup_(i <- s | P i) F i) X).
Proof.
apply/(iffP fsubsetP).
- move=> sub i i_s Pi; apply/fsubsetP=> x x_i.
  by apply: sub; apply/bigcupP; exists i.
- move=> sub x /bigcupP [i i_s Pi]; apply/fsubsetP; exact: sub.
Qed.

Lemma in_bigcup I (T : ordType) (P : I -> bool) (F : I -> {fset T}) s x :
  x \in \bigcup_(i <- s | P i) F i = has (fun i => P i && (x \in F i)) s.
Proof.
elim: s=> [|y s IH] /=; first by rewrite big_nil.
by rewrite big_cons; case: ifP; rewrite // in_fsetU IH.
Qed.

Lemma bigcup1_cond (T : ordType) (P : T -> bool) s :
  \bigcup_(x <- s | P x) fset1 x = fset [seq x <- s | P x].
Proof.
apply/eq_fset=> x; rewrite in_bigcup in_fset mem_filter.
apply/(sameP hasP)/(iffP andP).
  by case=> Px xs; exists x; rewrite // Px in_fset1 eqxx.
by case=> {}x xs /andP [] Px /fset1P ->.
Qed.

Lemma bigcup1 (T : ordType) (s : seq T) : \bigcup_(x <- s) fset1 x = fset s.
Proof. by rewrite bigcup1_cond filter_predT. Qed.

Lemma eq_mapm (T : ordType) S R (f g : S -> R) :
  f =1 g -> @mapm T S R f =1 mapm g.
Proof.
move=> e m; apply/eq_fmap=> x; rewrite !mapmE.
by case: (m x)=> [y|] //=; rewrite e.
Qed.

Lemma mapm_comp (T : ordType) S R U (g : R -> U) (f : S -> R) (m : {fmap T -> S}) :
  mapm (g \o f) m = mapm g (mapm f m).
Proof.
by apply/eq_fmap=> x; rewrite !mapmE; case: (m x).
Qed.

Lemma fmap_rect (T : ordType) S (P : {fmap T -> S} -> Type) :
  P emptym ->
  (forall m, P m -> forall x y, x \notin domm m -> P (setm m x y)) ->
  forall m, P m.
Proof.
move=> H0 H1 m; move e: (domm m)=> X.
elim/fset_rect: X m e=> [|x X x_X IH] m e.
  by move/eqP/emptymP: e=> ->.
have : x \in domm m by rewrite e in_fsetU1 eqxx.
rewrite mem_domm; case yP: (m x)=> [y|] // _.
set m' := remm m x; have em : m = setm m' x y.
  apply/eq_fmap=> x'; rewrite /m' setmE remmE.
  by case: eqP => [->|].
have {}e : domm m' = X.
  apply/eq_fset=> x'; rewrite /m' domm_rem e in_fsetD1 in_fsetU1.
  by case: eqP=> // -> /=; rewrite (negbTE x_X).
rewrite {}em; apply: H1; first by exact: IH.
by rewrite e.
Qed.

Lemma fmap_ind (T : ordType) S (P : {fmap T -> S} -> Prop) :
  P emptym ->
  (forall m, P m -> forall x y, x \notin domm m -> P (setm m x y)) ->
  forall m, P m.
Proof. exact: fmap_rect. Qed.

Lemma remmI (T : ordType) S (m : {fmap T -> S}) x :
  x \notin domm m ->
  remm m x = m.
Proof.
move=> /dommPn m_x; apply/eq_fmap=> x'; rewrite remmE.
by case: eqP=> // ->; rewrite m_x.
Qed.

Lemma setm_rem (T : ordType) S m (x : T) (y : S) :
  setm (remm m x) x y = setm m x y.
Proof.
apply/eq_fmap=> x'; rewrite !setmE !remmE.
by case: eqP.
Qed.

Lemma eq_setm (T : ordType) (S : eqType) m1 m2 (x : T) (y1 y2 : S) :
  (setm m1 x y1 == setm m2 x y2) =
  (y1 == y2) && (remm m1 x == remm m2 x).
Proof.
apply/(sameP eqP)/(iffP andP).
  rewrite -[setm m1 x y1]setm_rem.
  by case=> /eqP -> /eqP ->; rewrite setm_rem.
move=> /eq_fmap e.
move: (e x); rewrite !setmE eqxx; case=> ->; split=> //.
apply/eqP/eq_fmap=> x'; move: (e x'); rewrite !setmE !remmE.
by case: eqP.
Qed.

Lemma big_fsetU1 R (idx : R) (op : Monoid.com_law idx) (I : ordType) (x : I) (X : {fset I}) (P : pred I) (F : I -> R) :
  x \notin X ->
  let y := \big[op/idx]_(i <- X | P i) F i in
  \big[op/idx]_(i <- x |: X | P i) F i =
  if P x then op (F x) y else y.
Proof.
move=> x_X.
have e: perm_eq (x |: X) (x :: X).
  apply: uniq_perm; rewrite /= ?x_X ?uniq_fset // => x'.
  by rewrite inE in_fsetU1.
by rewrite /= (perm_big _ e) big_cons.
Qed.

Lemma val_fset_filter (T : ordType) (P : T -> bool) (X : {fset T}) :
  fset_filter P X = filter P X :> seq T.
Proof.
apply: (eq_sorted (@Ord.lt_trans T)).
- move=> x y /andP [/Ord.ltW xy /Ord.ltW yx].
  by apply: Ord.anti_leq; rewrite xy.
- rewrite /fset_filter /fset unlock /=.
  exact: FSet.fset_subproof.
- rewrite sorted_filter ?valP //.
  exact: Ord.lt_trans.
rewrite uniq_perm ?filter_uniq ?uniq_fset //.
by move=> x; rewrite /= in_fset_filter mem_filter.
Qed.

Lemma fset_filter_subset (T : ordType) (P : T -> bool) X :
  fsubset (fset_filter P X) X.
Proof.
by apply/fsubsetP=> x; rewrite in_fset_filter; case/andP.
Qed.

Lemma val_domm (T : ordType) (S : Type) (m : {fmap T -> S}) :
  domm m = unzip1 m :> seq _.
Proof.
apply: (eq_sorted (@Ord.lt_trans T)).
- move=> x y /andP [/Ord.ltW xy /Ord.ltW yx].
  by apply: Ord.anti_leq; rewrite xy.
- exact: valP.
- exact: (valP m).
rewrite uniq_perm // ?uniq_fset //.
  apply: sorted_uniq.
  - exact: (@Ord.lt_trans T).
  - exact: Ord.ltxx.
  - exact: (valP m).
by move=> x; rewrite in_fset.
Qed.

Lemma fmvalK (T : ordType) (S : Type) : cancel val (@mkfmap T S).
Proof.
by move=> /= m; apply/eq_fmap=> x; rewrite mkfmapE.
Qed.

Lemma mapim_map (T : ordType) (S R : Type) (f : S -> R) (m : {fmap T -> S}) :
  mapim (fun=> f) m = mapm f m.
Proof. by []. Qed.

Lemma mkfmapK (T : ordType) (S : Type) (kvs : seq (T * S)) :
  sorted Ord.lt (unzip1 kvs) ->
  mkfmap kvs = kvs :> seq (T * S).
Proof.
elim: kvs=> [|[k v] kvs IH]=> //= kvs_sorted.
rewrite IH ?(path_sorted kvs_sorted) //.
case: kvs kvs_sorted {IH} => [|[k' v'] kvs] //=.
by case/andP=> ->.
Qed.

Lemma getm_nth (T : ordType) (S : Type) p (m : {fmap T -> S}) i :
  i < size m ->
  m (nth p.1 (domm m) i) = Some (nth p m i).2.
Proof.
rewrite val_domm /getm; move: (valP m); rewrite /=.
elim: (val m) i=> [//|[/= k v] kv IH] [|i] /= kv_sorted.
  by rewrite eqxx.
rewrite ltnS=> isize; rewrite (IH _ (path_sorted kv_sorted) isize).
case: eqP=> // kP; have kkv: k \in unzip1 kv.
  by rewrite -kP; apply/mem_nth; rewrite size_map.
move/(order_path_min (@Ord.lt_trans T))/allP/(_ _ kkv): kv_sorted.
by rewrite Ord.ltxx.
Qed.

Arguments bigcupP {_ _ _ _ _ _}.
Arguments mkfmap {_ _}.
Arguments suppPn {_ _ _ _ _}.

Definition int_ordMixin := CanOrdMixin natsum_of_intK.
Canonical int_ordType := Eval hnf in OrdType int int_ordMixin.

Definition rat_ordMixin := [ordMixin of rat by <:].
Canonical rat_ordType := Eval hnf in OrdType rat rat_ordMixin.

Section FilterMap.

Variables T : ordType.
Variables S R : Type.

Definition filter_map (f : T -> S -> option R) (m : {fmap T -> S}) : {fmap T -> R} :=
  mkfmapfp (fun x => obind (f x) (m x)) (domm m).

Lemma filter_mapE f m x : filter_map f m x = obind (f x) (m x).
Proof.
by rewrite /filter_map mkfmapfpE mem_domm; case: (m x).
Qed.

Lemma domm_filter_map f m :
  domm (filter_map f m) = fset_filter (fun x => obind (f x) (m x)) (domm m).
Proof.
apply/eq_fset=> x.
by rewrite mem_domm filter_mapE in_fset_filter mem_domm andbC; case: (m x).
Qed.

Lemma mapimK (f : T -> R -> S) (g : T -> S -> option R) :
  (forall x y, g x (f x y) = Some y) ->
  cancel (mapim f) (filter_map g).
Proof.
move=> fK m; apply/eq_fmap=> x.
by rewrite filter_mapE mapimE; case: (m x)=> //= z.
Qed.

End FilterMap.

Lemma mapm_mkfmapf (T : ordType) (S R : Type) (f : S -> R) (g : T -> S)
  (X : {fset T}) : mapm f (mkfmapf g X) = mkfmapf (f \o g) X.
Proof.
by apply/eq_fmap=> x; rewrite !mapmE !mkfmapfE /=; case: ifP.
Qed.

Section SetSplitting.

Variables (T : ordType).

Implicit Types X : {fset T}.

Definition splits X :=
  if val X is x :: xs then Some (x, fset xs)
  else None.

End SetSplitting.

Section MapSplitting.

Variables (T : ordType) (S : Type).
Implicit Types m : {fmap T -> S}.

Definition splitm m :=
  match val m with
  | (x, y) :: ps => Some (x, y, mkfmap ps)
  | [::] => None
  end.

Lemma sizeES m :
  size m = if splitm m is Some (_, _, m') then (size m').+1 else 0.
Proof.
rewrite /splitm /=; move: (valP m)=> /=.
by case: (val m)=> [|[x y] m'] //= /path_sorted /mkfmapK ->.
Qed.

Lemma domm_mkfmap' (ps : seq (T * S)) :
  domm (mkfmap ps) = fset (unzip1 ps).
Proof.
by apply/eq_fset=> x; rewrite domm_mkfmap in_fset.
Qed.

Lemma dommES m :
  domm m = if splitm m is Some (x, _, m) then x |: domm m
           else fset0.
Proof.
rewrite /domm /splitm /=.
case: m=> [[|[x y] m] mP] //=; first by rewrite fset0E.
move: mP=> /= /path_sorted/mkfmapK ->.
by rewrite fset_cons.
Qed.

End MapSplitting.

Section Update.

Context {T : ordType} {S : eqType} {def : T -> S}.

Definition updm (f : ffun def) (xs : {fmap T -> S}) : ffun def :=
  mkffun (fun v => if xs v is Some x then x else f v)
         (supp f :|: domm xs).

Lemma updmE f xs x :
  updm f xs x = if xs x is Some y then y else f x.
Proof.
rewrite /updm mkffunE in_fsetU orbC mem_domm.
case e: (xs x)=> [y|] //=.
by case: ifPn=> // /suppPn ->.
Qed.

End Update.

Definition mkffunm (T : ordType) (S : eqType) (def : T -> S) (m : {fmap T -> S}) : ffun def :=
  mkffun (fun x => odflt (def x) (m x)) (domm m).

Lemma mkffunmE T S def m x :
  @mkffunm T S def m x = odflt (def x) (m x).
Proof.
by rewrite /mkffunm mkffunE mem_domm; case: (m x).
Qed.

Arguments fdisjointP {_ _ _}.

Definition mapf (T : ordType) (S R : eqType) (def : T -> S) (g : S -> R) (f : ffun def) : ffun (g \o def) :=
  mkffun (g \o f) (supp f).

Lemma mapfE (T : ordType) (S R : eqType) (def : T -> S) (g : S -> R) (f : ffun def) x :
  mapf g f x = g (f x).
Proof.
rewrite /mapf mkffunE mem_supp /=.
by case: eqP=> //= ->.
Qed.

Lemma val_mkffun (T : ordType) (S : eqType) (def : T -> S) (f : T -> S) (X : {fset T}) :
  @ffval _ _ def (mkffun f X) =
  mkfmapfp (fun x => if f x == def x then None else Some (f x)) X.
Proof.
apply/eq_fmap=> x; rewrite mkfmapfpE.
move: (@mkffunE _ _ def f X x); rewrite /appf /=.
set ff := mkffun f X; case e: (ffval ff x) => [y|].
- have xdomm: x \in domm (ffval ff) by rewrite mem_domm e.
  move/allP/(_ _ xdomm): (valP ff); rewrite /= e => yP ey.
  move: yP; rewrite {}ey; case: ifP; last by rewrite eqxx.
  rewrite inj_eq; last exact: Some_inj.
  by move=> _ /negbTE ->.
- by case: ifP=> // _ ->; rewrite eqxx.
Qed.

Lemma val_mapf (T : ordType) (S R : eqType) (def : T -> S) (g : S -> R) :
  injective g ->
  forall f : ffun def, ffval (mapf g f) = mapm g (ffval f).
Proof.
move=> g_inj f; apply/eq_fmap=> x.
rewrite /mapf val_mkffun mkfmapfpE mapmE mem_supp /= /appf /=.
rewrite inj_eq //.
case e: (ffval f x)=> [y|] /=; last by rewrite eqxx.
have xdomm: x \in domm (ffval f) by rewrite mem_domm e.
move/allP/(_ _ xdomm): (valP f); rewrite e.
rewrite inj_eq; last exact: Some_inj.
by move=> /negbTE ->.
Qed.

Lemma fset1_inj (T : ordType) : injective (@fset1 T).
Proof.
by move=> x y e; apply/fset1P; rewrite -e; apply/fset1P.
Qed.

Definition pimfset (T S : ordType) (f : T -> option S) (X : {fset T}) : {fset S} :=
  fset (pmap f X).

Lemma in_pimfset (T S : ordType) (f : T -> option S) (X : {fset T}) y :
  y \in (pimfset f X) = (Some y \in f @: X).
Proof.
rewrite /pimfset in_fset mem_pmap.
by apply/(sameP mapP)/(iffP imfsetP).
Qed.

Lemma pimfsetP (T S : ordType) (f : T -> option S) (X : {fset T}) y :
  reflect (exists2 x, x \in X & f x = Some y) (y \in pimfset f X).
Proof.
rewrite in_pimfset; apply/(iffP imfsetP); case=> ??.
- by move=> ->; eauto.
- by move=> <-; eauto.
Qed.

Lemma supp_mkffun_subset (T : ordType) (S : eqType) (def f : T -> S) (X : {fset T}) :
  fsubset (supp (@mkffun _ _ def f X)) X.
Proof.
rewrite supp_mkffun; apply/fsubsetP=> x; rewrite in_fset mem_filter.
by case/andP.
Qed.
