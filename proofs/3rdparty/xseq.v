(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect eqtype ssrbool ssrfun ssrnat.
From mathcomp Require Export seq.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition pair_inj {A B: Type} {a a': A} {b b': B} (e: (a, b) = (a', b')) :
  a = a' ∧ b = b' :=
  let 'Logic.eq_refl := e in conj Logic.eq_refl Logic.eq_refl.

(* -------------------------------------------------------------------- *)
Section Assoc.
Variable (T : eqType) (U : Type).

Fixpoint assoc (s : seq (T * U)) (x : T) : option U :=
  if s is (y, v) :: s then
    if x == y then Some v else assoc s x
  else None.

Lemma assoc_cat (s1 s2: seq (T * U)) x :
  assoc (s1 ++ s2) x =
    if assoc s1 x is Some _ then assoc s1 x else assoc s2 x.
Proof. by elim: s1 => [|[t u] s1 ih] //=; case: eqP. Qed.
End Assoc.

Lemma assocE (T: eqType) U (s : seq (T * U)) (x : T) : assoc s x =
  nth None [seq Some v.2 | v <- s] (seq.index x [seq v.1 | v <- s]).
Proof.
by elim: s => // [[/= u v] s ih]; rewrite [x==u]eq_sym; case: eqP.
Qed.

Lemma assoc_mem' (T: eqType) U (s: seq (T * U)) x w :
  assoc s x = Some w → List.In (x, w) s.
Proof.
  elim: s => // [ [t u] s ] ih /=; case: eqP; last by auto.
  by move => a b; apply Some_inj in b; left; f_equal.
Qed.

Lemma mem_assoc (T: eqType) U (s: seq (T * U)) x w :
  List.In (x, w) s → ∃ w', assoc s x = Some w'.
Proof.
  elim: s => // [ [t u] s] ih [ /pair_inj [] -> -> | rec ] /=.
  by rewrite eq_refl; eauto.
  case: (_ == _); eauto.
Qed.

Lemma InP (T: eqType) (s: seq T) m :
  reflect (List.In m s) (m \in s).
Proof.
  elim: s. by constructor.
  move => a s ih. rewrite in_cons.
  case: (@eqP _ m a). by constructor; left.
  case ih; constructor. by right. simpl; intuition.
Qed.

Lemma mem_uniq_assoc (T: eqType) U (s: seq (T * U)) x w :
  List.In (x, w) s → uniq (map fst s) → assoc s x = Some w.
Proof.
  elim: s => // [ [t u] s] ih [ /pair_inj [] -> -> | rec ] /andP [nr un] /=.
  by rewrite eq_refl; eauto.
  case: eqP; last by eauto.
  fold (List.In (x, w) s) in rec.
  apply (List.in_map fst), (rwP (InP _ _)) in rec.
  move=> ?; subst. rewrite rec in nr. done.
Qed.

Lemma assoc_mem_dom' (T: eqType) U (s : seq (T * U)) x w :
  assoc s x = Some w -> x \in [seq v.1 | v <- s].
Proof. move => h; apply assoc_mem' in h. apply (rwP (InP _ _)), List.in_map_iff. eexists; split. 2: eassumption. reflexivity. Qed.

(* -------------------------------------------------------------------- *)
Section AssocInj.
Variables (T U: eqType).

Lemma assocP (s : seq (T * U)) (x : T) (w : U) : uniq (map fst s) ->
  reflect (assoc s x = Some w) ((x, w) \in s).
Proof.
elim: s => [|[t u] s ih] => uq; first by constructor.
move: uq => /andP[/= t_notin_s /ih {ih}]; move: t_notin_s.
case: eqP=> [->|/eqP ne_xt] t_notin_s; last first.
+ by rewrite in_cons eqE /= (negbTE ne_xt).
rewrite inE eqE /= eqxx /=; case: eqP => [->|ne_wu] _ /=.
+ by constructor.
suff ->: (t, w) \in s = false by constructor; case=> /esym.
by apply/negbTE; apply/contra: t_notin_s => /(map_f fst).
Qed.

Lemma assoc_mem (s : seq (T * U)) x w :
  assoc s x = Some w -> (x, w) \in s.
Proof.
elim: s => [|[t u] s ih] //=; case: eqP => [-> [->]|/eqP ne].
+ by rewrite in_cons eqxx orTb.
by rewrite in_cons eqE /= (negbTE ne).
Qed.

Lemma assoc_mem_dom (s : seq (T * U)) x w :
  assoc s x = Some w -> w \in [seq v.2 | v <- s].
Proof. by move/assoc_mem/(map_f snd). Qed.

Lemma assoc_inj (s : seq (T * U)) x y w :
     uniq [seq v.2 | v <- s]
  -> assoc s x = Some w
  -> assoc s y = Some w
  -> x = y.
Proof.
elim: s => [|[t u] s ih] //= /andP[u_notin_s uq_s xw yx].
move: xw yx ih u_notin_s; case: eqP => [-> [->]|ne_xt].
+ by case: eqP=> [->//|] ne_yt yw _ /negbTE; rewrite (assoc_mem_dom yw).
move=> xw; case: eqP=> [-> [->] _|].
+ by move/negbTE; rewrite (assoc_mem_dom xw).
by move=> ne_yt yw ih u_notin_s; apply: ih.
Qed.
End AssocInj.

(* -------------------------------------------------------------------- *)
Section InjAssoc.
Variables (T U : eqType) (f : T -> U).

Lemma inj_assoc (s : seq T) x y w :
     uniq s
  -> assoc [seq (f v, v) | v <- s] x = Some w
  -> assoc [seq (f v, v) | v <- s] y = Some w
  -> x = y.
Proof.
by move=> uq_s; apply: assoc_inj; rewrite -map_comp map_inj_uniq.
Qed.
End InjAssoc.

(* -------------------------------------------------------------------- *)
Section AssocMap.
Context (T: eqType) (U V: Type) (f: U → V).

Lemma assoc_map m (n: T) :
  assoc [seq (x.1, f x.2) | x <- m] n = omap f (assoc m n).
Proof.
  by elim: m n => // [[q r] m] ih n /=; case: eqP.
Qed.

End AssocMap.

(* -------------------------------------------------------------------- *)
Section AssocFilter.
Context (T: eqType) (U: Type) (p: pred T).

Lemma neq (x y: T) (n: x ≠ y) : x == y = false.
Proof. by case: eqP. Qed.

Lemma assoc_filter (m: seq (T * U)) (n: T) :
  p n →
  assoc [seq x <- m | p x.1] n = assoc m n.
Proof.
  elim: m n => // [[q r] m ] ih n hn /=; case: eqP.
  + by move => <- {q}; rewrite hn /= eq_refl.
  move=> ne; case: (p _); auto; rewrite /= neq; auto.
Qed.

End AssocFilter.