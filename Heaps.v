
From Coq Require Import ZArith Lia Bool String List.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Common.

Local Open Scope Z_scope.

(** * 1. Memory heaps *)

(** A memory heap is a partial function from addresses (memory locations) 
    to values, with a finite domain. *)

Definition addr := Z.

Record heap (A:Type) : Type := {
  contents :> addr -> option A;
  isfinite : exists i, forall j, i <= j -> contents j = None
}.

Lemma heap_extensionality:
  forall (A:Type) (h1 h2: heap A),
  (forall l, h1 l = h2 l) -> h1 = h2.
Proof.
  intros. destruct h1 as [c1 fin1], h2 as [c2 fin2].
  assert (c1 = c2) by (apply functional_extensionality; auto).
  subst c2. f_equal. apply proof_irrelevance.
Qed.

(** The empty heap. *)

Program Definition hempty {A:Type} : heap A :=
  {| contents := fun l => None |}.
Next Obligation.
  exists 0; auto.
Qed.

(** The heap that contains [v] at address [l] and is equal to [h] on
    all other addresses. *)

Program Definition hupdate {A:Type} (l: addr) (v: A) (h: heap A) : heap A :=
  {| contents := fun l' => if Z.eq_dec l l' then Some v else h l' |}.
Next Obligation.
  destruct (isfinite A h) as (i & fin).
  exists (Z.max i (l + 1)); intros.
  destruct (Z.eq_dec l j). lia. apply fin; lia.
Qed.

Lemma hupdate_same: forall {A:Type} l (v:A) h, (hupdate l v h) l = Some v.
Proof.
  intros; cbn. destruct (Z.eq_dec l l); congruence.
Qed.

Lemma hupdate_other: forall {A:Type} l (v:A) h l', l <> l' -> (hupdate l v h) l' = h l'.
Proof.
  intros; cbn. destruct (Z.eq_dec l l'); congruence.
Qed.

Definition hsingle {A:Type} (l: addr) (v: A) : heap A :=
  hupdate l v hempty.

(** The heap [h] after deallocating address [l]. *)

Program Definition hfree {A:Type} (l: addr) (h: heap A) : heap A :=
  {| contents := fun l' => if Z.eq_dec l l' then None else h l' |}.
Next Obligation.
  destruct (isfinite A h) as (i & fin).
  exists i; intros. destruct (Z.eq_dec l j); auto.
Qed.

(** The heap [h] where addresses [l, ..., l + sz - 1] are initialized to 0. *)

(* Fixpoint hinit {A:Type} (l: addr) (sz: nat) (h: heap A) : heap A :=
  match sz with O => h | S sz => hupdate l 0 (hinit (l + 1) sz h) end.

Lemma hinit_inside:
  forall h sz l l', l <= l' < l + Z.of_nat sz -> hinit l sz h l' = Some 0.
Proof.
  induction sz; intros; cbn.
- lia.
- destruct (Z.eq_dec l l'); auto. apply IHsz. lia.
Qed.

Lemma hinit_outside:
  forall h sz l l', l' < l \/ l + Z.of_nat sz <= l' -> hinit l sz h l' = h l'.
Proof.
  induction sz; intros; cbn.
- auto.
- destruct (Z.eq_dec l l'). lia. apply IHsz; lia.
Qed. *)

(** The disjoint union of two heaps. *)

Definition hdisjoint {A:Type} (h1 h2: heap A) : Prop :=
  forall l, h1 l = None \/ h2 l = None.

Lemma hdisjoint_sym:
  forall {A:Type} (h1 h2:heap A), hdisjoint h1 h2 <-> hdisjoint h2 h1.
Proof.
  unfold hdisjoint; intros; split; intros H l; specialize (H l); tauto.
Qed.

Program Definition hunion {A:Type} (h1 h2: heap A) : heap A :=
  {| contents := fun l => if h1 l then h1 l else h2 l |}.
Next Obligation.
  destruct (isfinite A h1) as (i1 & fin1), (isfinite A h2) as (i2 & fin2).
  exists (Z.max i1 i2); intros. rewrite fin1, fin2 by lia. auto.
Qed.

Lemma hunion_comm:
  forall {A:Type} (h1 h2:heap A), hdisjoint h1 h2 -> hunion h2 h1 = hunion h1 h2.
Proof.
  intros; apply heap_extensionality; intros; cbn.
  specialize (H l). destruct (h1 l), (h2 l); intuition congruence.
Qed.

Lemma hunion_assoc:
  forall {A:Type} (h1 h2 h3:heap A), hunion (hunion h1 h2) h3 = hunion h1 (hunion h2 h3).
Proof.
  intros; apply heap_extensionality; intros; cbn. destruct (h1 l); auto.
Qed.

Lemma hunion_empty:
  forall {A:Type} (h:heap A), hunion hempty h = h.
Proof.
  intros; apply heap_extensionality; intros; cbn. auto.
Qed.

Lemma hunion_refl:
  forall {A:Type} (h: heap A), hunion h h = h.
Proof.
  intros; apply heap_extensionality; intros; cbn.
  destruct (h l); auto.
Qed.

(* Lemma hfree_hunion_hupdate:
  forall h l v,
  hdisjoint (hupdate l v hempty) h ->
  hfree l (hunion (hupdate l v hempty) h) = h.
Proof.
  intros; apply heap_extensionality; intros; cbn.
  (* l is the location that is not in h *)
  (* l0 is an arb location *)
  destruct (Z.eq_dec l l0).
  - (* suppose l0 is the location that is not in h.
      use disjointness to show l0/l is not in h *)
    subst.
    unfold hdisjoint in H.
    pose proof (H l0) as H0; destruct H0.
    + rewrite hupdate_same in H0.
      discriminate H0.
    + auto.
  - destruct (h l0); auto.
Qed. *)

Lemma hdisjoint_empty:
  forall {A:Type} (h:heap A), hdisjoint hempty h.
Proof.
  intros.
  unfold hdisjoint; intros.
  left.
  reflexivity.
Qed.

Lemma hdisjoint_union_l:
  forall {A:Type} (h1 h2 h3: heap A),
  hdisjoint (hunion h1 h2) h3 <-> hdisjoint h1 h3 /\ hdisjoint h2 h3.
Proof.
  unfold hdisjoint, hunion; cbn; intros. split.
- intros D; split; intros l; destruct (D l); auto; destruct (h1 l); auto.
  discriminate.
- intros [D1 D2] l. destruct (D2 l); auto. destruct (h1 l) eqn:H1; auto. destruct (D1 l); auto. congruence.
Qed.

Lemma hdisjoint_union_r:
  forall {A:Type} (h1 h2 h3: heap A),
  hdisjoint h1 (hunion h2 h3) <-> hdisjoint h1 h2 /\ hdisjoint h1 h3.
Proof.
  intros. rewrite hdisjoint_sym. rewrite hdisjoint_union_l. 
  rewrite (hdisjoint_sym h2), (hdisjoint_sym h3). tauto.
Qed.

(** Disjointness between three heaps. *)

Definition hdisj3 {A:Type} (h1 h2 h3: heap A) :=
  hdisjoint h1 h2 /\ hdisjoint h1 h3 /\ hdisjoint h2 h3.

(** A tactic to prove disjointness statements. *)

Ltac HDISJ :=
  match goal with
  | [ H: hdisj3 _ _ _ |- _ ] =>
      destruct H as (? & ? & ?); HDISJ
  | [ H: hdisjoint (hunion _ _) _ |- _ ] =>
      apply hdisjoint_union_l in H; destruct H; HDISJ
  | [ H: hdisjoint _ (hunion _ _) |- _ ] =>
      apply hdisjoint_union_r in H; destruct H; HDISJ
  | [ |- hdisj3 _ _ _ ] =>
      split; [|split]; HDISJ
  | [ |- hdisjoint (hunion _ _) _ ] =>
      apply hdisjoint_union_l; split; HDISJ
  | [ |- hdisjoint _ (hunion _ _) ] =>
      apply hdisjoint_union_r; split; HDISJ
  | [ |- hdisjoint hempty _ ] =>
      red; auto
  | [ |- hdisjoint _ hempty ] =>
      red; auto
  | [ |- hdisjoint _ _ ] =>
      assumption || (apply hdisjoint_sym; assumption) || idtac
  | _ => idtac
  end.

Lemma hunion_invert_r:
  forall {A:Type} (h1 h2 h:heap A),
  hunion h h1 = hunion h h2 -> hdisjoint h h1 -> hdisjoint h h2 -> h1 = h2.
Proof.
  intros. apply heap_extensionality; intros l.
  assert (hunion h h1 l = hunion h h2 l) by congruence.
  cbn in H2. specialize (H0 l); specialize (H1 l). destruct (h l); intuition congruence.
Qed.

Lemma hunion_invert_l:
  forall {A:Type} (h1 h2 h: heap A),
  hunion h1 h = hunion h2 h -> hdisjoint h1 h -> hdisjoint h2 h -> h1 = h2.
Proof.
  intros. apply hunion_invert_r with h.
  rewrite <- ! (hunion_comm h) by HDISJ. auto.
  HDISJ. HDISJ.
Qed. 