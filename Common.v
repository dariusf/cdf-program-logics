
From CDF Require Import Tactics.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From Coq Require Import ZArith Lia Bool List String Program.Equality.
Local Open Scope Z_scope.

Local Open Scope string_scope.

Definition ident := string.

Section Store.

  Definition store (A:Type) : Type := ident -> option A.
  Definition sempty {A:Type} : store A := (fun _ => None).
  Definition supdate {A:Type} (x: ident) (v: A) (s: store A) : store A :=
    fun y => if string_dec x y then Some v else s y.
  Definition sremove {A:Type} (x: ident) (s: store A) : store A :=
    fun y => if string_dec x y then None else s y.

  Lemma sremove_any: forall l A (s : store A),
    (sremove l s) l = None.
  Proof.
    intros; cbn.
    unfold sremove.
    destruct (string_dec l l).
    auto.
    easy.
  Qed.

  Lemma supdate_same: forall A (h:store A) v l,
    (supdate l v h) l = Some v.
  Proof.
    intros; cbn.
    unfold supdate.
    destruct (string_dec l l); congruence.
  Qed.

  Lemma supdate_noop : forall A s x (v:A), s x = Some v -> supdate x v s = s.
  Proof.
    intros.
    unfold supdate.
    apply functional_extensionality.
    intros.
    destruct (string_dec x x0).
    - congruence.
    - reflexivity.
  Qed.

  Lemma supdate_other: forall A (h:store A) l v l',
    l <> l' -> (supdate l v h) l' = h l'.
  Proof.
    intros; cbn.
    unfold supdate.
    destruct (string_dec l l'); congruence.
  Qed.

  Lemma supdate_dupe : forall {A} (v:A) x s,
    supdate x v (supdate x v s) = supdate x v s.
  Proof.
    intros.
    unfold supdate.
    apply functional_extensionality.
    intros.
    destruct (string_dec x x0); easy.
  Qed.

  (* s1 <= s2 *)
  Definition substore {A:Type} (s1 s2 : store A) :=
    forall v x, s1 x = Some v -> s2 x = Some v.

  Lemma substore_notin : forall A (s:store A) v x y,
    s x = None -> s y = Some v -> x <> y.
  Proof.
    intros.
    unfold substore in H.
    unfold substore; intros.
    unfold not; intros.
    congruence.
  Qed.

  Lemma substore_extension : forall A (s2:store A) v x,
    s2 x = None -> substore s2 (supdate x v s2).
  Proof.
    intros.
    unfold substore in H.
    unfold substore; intros.
    rewrite <- H0.
    apply supdate_other.
    apply substore_notin with (s:=s2) (v:=v0); auto.
  Qed.

  Lemma substore_refl : forall A (s1:store A),
    substore s1 s1.
  Proof.
    now unfold substore.
  Qed.

  Lemma substore_trans : forall A (s1 s2 s3: store A),
    substore s1 s2 -> substore s2 s3 -> substore s1 s3.
  Proof.
    intros.
    unfold substore in H.
    unfold substore in H0.
    unfold substore; intros.
    apply H0.
    now apply H.
  Qed.

  Lemma substore_extension_trans : forall A (s1 s2: store A) v x,
    substore s1 s2 -> s2 x = None -> substore s1 (supdate x v s2).
  Proof.
    intros.
    assert (substore s2 (supdate x v s2)).
    now apply substore_extension.
    now apply substore_trans with (s2 := s2).
  Qed.

  Lemma substore_extension_inv : forall A (s1 s2:store A) v x,
    substore (supdate x v s1) s2 ->
    s2 x = Some v.
  Proof.
    unfold substore; intros.
    apply H.
    rewrite supdate_same.
    auto.
  Qed.

  Lemma substore_mem : forall A (s1 s2:store A) v x,
    substore s1 s2 ->
    s1 x = Some v ->
    s2 x = Some v.
  Proof.
    unfold substore; intros.
    apply H.
    easy.
  Qed.

  (** This can't be proved, as substore only concerns bindings which are present *)
  Lemma substore_mem_contra : forall A (s1 s2:store A) x,
    substore s1 s2 ->
    s2 x = None ->
    s1 x = None.
  Proof.
    unfold substore; intros.
  Abort.

  Lemma substore_extension_left : forall A (s1 s2:store A) v x,
    substore s1 s2 ->
    s2 x = Some v ->
    substore (supdate x v s1) s2.
  Proof.
    unfold substore; intros.
    unfold supdate in H1.
    destruct (string_dec x x0).
    - 
    (* if x is in s1, then updating it must have no effect *)
    rewrite H1 in H0.
    rewrite e in H0.
    assumption.
    - 
    (* if x is not in s1, then updating it grows s1, but the result is no larger than s2 *)
    apply H.
    assumption.
  Qed.

  Lemma substore_empty : forall (A:Type) s, @substore A sempty s.
  Proof.
    unfold substore.
    unfold sempty.
    ok.
  Qed.

  (** The converse is not true. Consider: (x=1)[x:=2] <= (y=1)[x:=2] *)
  Lemma substore_aug : forall A x (v:A) s1 s2,
    substore s1 s2 ->
    substore (supdate x v s1) (supdate x v s2).
  Proof.
    intros.
    unfold substore.
    intros.
    destruct (string_dec x x0).
    - subst.
      unfold supdate in H0.
      unfold supdate.
      destruct (string_dec x0 x0).
      inj H0.
      ok.
      ok.
    - unfold substore in H.
      rewrite supdate_other; auto.
      pose proof (supdate_other A s1 x v x0 n).
      rewrite H1 in H0.
      apply H.
      auto.
  Qed.

  (** A restricted version of the converse is true, however. *)
  Lemma substore_reduce_left : forall A x (v:A) s1 s2,
    (* this guarantees removing the update on the left side shrinks it *)
    s1 x = None ->
    substore (supdate x v s1) s2 ->
    substore s1 s2.
  Proof.
    intros.
    unfold substore. intros.
    unfold substore in H0.
    apply H0.
    destruct (string_dec x x0).
    - subst.
      congruence.
    - rewrite supdate_other; auto.
  Qed.

End Store.

Section Well_founded_Nat.

  Local Open Scope nat_scope.
  Variable A : Type.

  Variable f : A -> nat.
  Definition ltof (a b:A) := f a < f b.
  Definition gtof (a b:A) := f b > f a.

  Theorem well_founded_ltof : well_founded ltof.
  Proof.
    unfold well_founded.
    assert (H : forall n (a:A), f a < n -> Acc ltof a).
    { intro n; induction n as [|n IHn].
      - intros a Ha; absurd (f a < 0); auto. apply Nat.nlt_0_r.
      - intros a Ha. apply Acc_intro. unfold ltof at 1. intros b Hb.
        apply IHn. apply Nat.lt_le_trans with (f a); auto. now apply Nat.succ_le_mono. }
    intros a. apply (H (S (f a))). apply Nat.lt_succ_diag_r.
  Defined.

End Well_founded_Nat.

Inductive nati := n (n:nat) | inf.

Coercion n : nat >-> nati.
Declare Scope nati_scope.
Delimit Scope nati_scope with nati.
Notation "∞" := inf : nati_scope.

Definition nati_le (a b:nati) : Prop :=
  match a, b with
  | n a, n b => (a<=b)%nat
  | n _, inf => True
  | inf, n _ => False
  | inf, inf => True
  end.

Definition nati_plus (a b:nati) : nati :=
  match a, b with
  | n a, n b => n (a+b)%nat
  | n _, inf => inf
  | inf, n _ => inf
  | inf, inf => inf
  end.

Notation "x >= y" := (nati_le y x) : nati_scope.
Notation "x > y" := (nati_le y x /\ y <> x) : nati_scope.
Notation "x <= y" := (nati_le x y) : nati_scope.
Notation "x + y" := (nati_plus x y) : nati_scope.
Bind Scope nati_scope with nati.

Local Open Scope nat_scope.

Lemma nati_plus_0 : forall a, (a + 0)%nati = a.
Proof.
  intros. destruct a.
  - simpl. now rewrite Nat.add_0_r.
  - simpl. reflexivity.
Qed.

Lemma nati_0_plus : forall a, (0 + a)%nati = a.
Proof.
  intros. destruct a.
  - now simpl.
  - simpl. reflexivity.
Qed.

Lemma nati_le_move : forall a b c,
  (c > 0)%nat ->
  (a + S b <= n c <-> a + b <= Nat.pred c)%nati.
Proof.
  destruct a.
  - induction n0.
    + simpl; split; lia.
    + split; intros.
    * simpl in H0.
      simpl.
      rewrite plus_n_Sm.
      apply (IHn0 _ c). auto.
      simpl.
      rewrite plus_n_Sm in H0.
      assumption.
    * simpl.
      rewrite plus_n_Sm.
      apply IHn0. assumption.
      simpl in H0.
      rewrite plus_n_Sm in H0.
      assumption.
  - intuition.
Qed.

Lemma nati_ge_move : forall a b c,
  (c > 0)%nat ->
  (a + S b >= n c <-> a + b >= Nat.pred c)%nati.
Proof.
  destruct a.
  - induction n0.
    + simpl; split; lia.
    + split; intros.
    * simpl in H0.
      simpl.
      rewrite plus_n_Sm.
      apply (IHn0 _ c). auto.
      simpl.
      rewrite plus_n_Sm in H0.
      assumption.
    * simpl.
      rewrite plus_n_Sm.
      apply IHn0. assumption.
      simpl in H0.
      rewrite plus_n_Sm in H0.
      assumption.
  - intuition.
Qed.


Lemma geq_succ : forall m n, n >= S m -> n > 0.
Proof.
  lia.
Qed.

Lemma nati_plus_le : forall a b c,
  (c >= b)%nat -> (a + n b <= n c <-> a <= c - b)%nati.
Proof.
  induction b; intros.
  - rewrite nati_plus_0.
    rewrite Nat.sub_0_r.
    intuition.
  - pose proof (geq_succ _ _ H).
    assert (forall b c, (c > 0)%nat -> (c - S b = Nat.pred c - b))%nati. lia.
    rewrite nati_le_move; auto.
    rewrite H1; auto.
    apply IHb.
    lia.
Qed.

Lemma nati_plus_ge : forall a b c,
  (c >= b)%nat -> (a + n b >= n c <-> a >= c - b)%nati.
Proof.
  induction b; intros.
  - rewrite nati_plus_0.
    rewrite Nat.sub_0_r.
    intuition.
  - pose proof (geq_succ _ _ H).
    assert (forall b c, (c > 0)%nat -> (c - S b = Nat.pred c - b))%nati. lia.
    rewrite nati_ge_move; auto.
    rewrite H1; auto.
    apply IHb.
    lia.
Qed.

Lemma nati_le_inf : forall a n,
  (a + n <= inf <-> a <= inf)%nati.
Proof.
  destruct a.
  - destruct n.
    + simpl. split. easy. destruct n2; easy.
    + intros. simpl. split. easy. destruct n1; easy.
  - simpl. split. easy. destruct n0; easy.
Qed.

Lemma nati_le_inf_r : forall a m,
  (a <= inf + m <-> a <= inf)%nati.
Proof.
  destruct a.
  - destruct n.
    + simpl. split. easy. destruct m; easy.
    + intros. simpl. split. easy. destruct m; easy.
  - simpl. split. easy. destruct m; easy.
Qed.

Lemma nati_le_antisymm : forall n m,
  (n <= m -> m <= n -> n = m)%nati.
Proof.
  intros n m H1 H2.
  unfold nati_le in H1.
  unfold nati_le in H2.
  destruct n; destruct m.
  - f_equal.
    apply Nat.le_antisymm.
    auto. auto.
  - easy.
  - easy.
  - easy.
Qed.

Lemma nati_zero_smallest : forall a, (0 <= a)%nati.
Proof.
  intros.
  unfold nati_le. destruct a. lia. easy.
Qed.

Lemma inf_greatest : forall a, (a <= inf)%nati.
Proof.
  intros.
  unfold nati_le. destruct a; easy.
Qed.

Lemma inf_inf : forall a,
  ~ (inf = n a).
Proof.
  unfold not; intros.
  inversion H.
Qed.

Lemma is_inf : forall a, (a >= inf)%nati <-> a = inf.
Proof.
  destruct a; easy.
Qed.

Lemma nati_n_ge_inf : forall (a:nati) (n:nat),
  (a + n >= inf <-> a = inf)%nati.
Proof.
  destruct a; easy.
Qed.
