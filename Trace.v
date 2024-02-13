
From Coq Require Import ZArith Lia Bool List String Program.Equality.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Separation.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope nat_scope.
Local Open Scope list_scope.

Lemma hdisjoint_empty_r:
  forall h, hdisjoint h hempty.
Proof.
  cbn. intros. right. cbn. reflexivity.
Qed.

Lemma hdisjoint_empty:
  forall h, hdisjoint hempty h.
Proof.
  intros.
  apply hdisjoint_sym.
  apply hdisjoint_empty_r.
Qed.

Lemma hunion_empty_r:
  forall h, hunion h hempty = h.
Proof.
  intros.
  pose proof (hdisjoint_empty_r h).
  rewrite hunion_comm.
  apply hunion_empty.
  apply hdisjoint_empty.
Qed.

Definition any : assertion :=
  fun h => True.

Section Trace.

(* possibly-infinite sequence of heaps *)
Definition trace : Type := nat -> heap.

(* offset a trace, e.g. offset 1 t = tail t *)
Definition offset (n : nat) (t: trace) : trace :=
  fun m => t (m + n).

(* assertions on traces *)
Definition flow : Type := trace -> Prop.

(* the first element of the trace is h1 + h2. h1 is the piece of heap satisfying the assertion, h2 is what is leftover *)
Definition req (P: assertion) : flow :=
  fun t => exists h1 h2,
    t 0 = hunion h1 h2 /\ hdisjoint h1 h2 /\ P h1 /\ t 1 = h2.

Definition ens (P: assertion) : flow :=
  fun t => exists h1,
    P h1 /\ t 1 = hunion (t 0) h1 /\ hdisjoint (t 0) h1.

(* TODO postcondition *)

Definition seq (f1 f2 : flow) : flow :=
  fun t => f1 t /\ f2 (offset 1 t).

(* TODO what is the semantics of functions? *)
(* TODO how to represent res variable? *)

Definition fn (name : string) : flow :=
  fun _ => True.

Definition e1_trace x := (fun t => if t =? 0 then (hupdate x 1 hempty) else if t =? 1 then hempty else (hupdate x 2 hempty)).

Example e1 : forall x, (seq (req (contains x 1)) (ens (contains x 2))) (e1_trace x).
Proof.
  intros.
  unfold seq; split.
  - unfold req.
    exists (hupdate x 1 hempty).
    exists hempty.
    repeat split.
    + cbn. rewrite hunion_empty_r. reflexivity.
    + apply hdisjoint_empty_r.
  - cbn.
    unfold ens.
    exists (hupdate x 2 hempty).
    repeat split.
    + cbn. rewrite hunion_empty. reflexivity.
    + cbn. apply hdisjoint_empty.
Qed.

(* TODO frame rule *)

Local Open Scope Z_scope.

Definition pt (l: addr) (v: Z) : assertion :=
  fun h => h l = Some v.

(* this doesn't use the assertion language, which seems error-prone, e.g. x may be equal to y *)
Example e21 : forall x y,
  aimp
    (fun h => h x = Some 1 /\ h y = Some 2)
    (fun h => h x = Some 1).
Proof.
  intros.
  unfold aimp; intros.
  unfold sepconj in H.
  destruct H.
  auto.
Qed.

Lemma sem_frame : forall h h1 h2 x v,
  h = hunion h1 h2 -> hdisjoint h1 h2 ->
  pt x v h1 ->
  pt x v (hunion h1 h2).
Proof.
  intros.
  unfold pt.
  unfold pt in H1.
  unfold hunion; simpl.
  rewrite H1.
  auto.
Qed.

Lemma sem_frame_r : forall h h1 h2 x v,
  h = hunion h1 h2 -> hdisjoint h1 h2 ->
  pt x v h2 ->
  pt x v (hunion h1 h2).
Proof.
  intros.
  unfold pt.
  unfold pt in H1.
  unfold hunion; simpl.
  rewrite H1.
  unfold hdisjoint in H0.
  specialize (H0 x).
  destruct H0.
  - rewrite H0. auto.
  - rewrite H0 in H1. discriminate H1.
Qed.

Example e2 : forall x y,
  aimp
    (pt x 1 ** pt y 2)
    (pt x 1).
Proof.
  intros.
  unfold aimp; intros.
  unfold sepconj in H.
  destruct H as [h1 [h2 [H1 [H2 [H3 H4]]]]].
  unfold pt in H1.
  rewrite H4.
  unfold pt.
  apply (sem_frame h _ _ _ _); auto.
Qed.

Example e22 : forall x,
  aimp
    (pt x 1)
    emp.
Proof.
  intros.
  unfold aimp; intros.
  unfold emp.
  unfold pt in H.
  (* doesn't work due to needing frame inference *)
Abort.

Example e23 : forall x,
  aimp
    (pt x 1)
    any.
Proof.
  intros.
  unfold aimp; intros.
  unfold any.
  reflexivity.
Qed.

Local Open Scope nat_scope.

(* this is entailment between traces *)
Definition entails (f1 f2 : flow) : Prop := 
  forall t, f1 t -> f2 t.

Definition entailv (v : trace -> Prop) (f1 f2 : flow) : Prop := 
  forall t, v t -> f1 t -> f2 t.

Lemma pt_hupdate_same : forall x v h,
  pt x v h ->
  hupdate x v h = h.
Proof.
  intros.
  apply heap_extensionality; intros.
  simpl.
  destruct (Z.eq_dec x l).
  - rewrite <- H. rewrite e. auto.
  - reflexivity.
Qed.

Lemma hdisjoint_hupdate_hfree : forall x v h,
  hdisjoint (hupdate x v hempty) (hfree x h).
Proof.
  intros.
  unfold hdisjoint; intros.
  destruct (Z.eq_dec x l).
  - right. rewrite e. unfold hfree. simpl. destruct (Z.eq_dec l l). reflexivity. exfalso. unfold not in n. apply n. auto.
  - left. unfold hupdate. simpl. destruct (Z.eq_dec x l). exfalso. apply n. auto. auto.
Qed.

Lemma hunion_hupdate_hfree : forall x v h,
  hunion (hupdate x v hempty) (hfree x h) = hupdate x v h.
Proof.
  intros.
  apply heap_extensionality; intros.
  unfold hunion.
  simpl.
  destruct (Z.eq_dec x l).
  - auto.
  - reflexivity.
Qed.

Lemma pt_hunion_hupdate_free : forall x v h,
  pt x v h ->
  hunion (hupdate x v hempty) (hfree x h) = h.
Proof.
  intros.
  pose proof (pt_hupdate_same _ _ _ H).
  rewrite <- H0 at 2.
  apply hunion_hupdate_hfree.
Qed.

Example e3 : forall x,
  entailv (fun t => pt x 1 (t 0))
    (req emp)
    (req (pt x 1)).
Proof.
  intros.
  unfold entailv; intros.
  unfold req in H0.
  destruct H0 as [h1 [h2 [H1 [H2 [H3]]]]].
  unfold emp in H3.
  (* h1 is empty, h2 = t 0 = t 1 *)

  unfold req.
  (* h0 is x->1, h3 is h2-h0 *)
  exists (hupdate x 1 hempty).
  (* pose proof (exists h3, h2 = hunion h4 h3). *)
  exists (hfree x h2).
  repeat split.
  - rewrite H3 in H1.
    rewrite hunion_empty in H1.
    rewrite <- H1.
    pose proof (pt_hunion_hupdate_free _ _ _ H).
    rewrite H4. auto.
  - apply hdisjoint_hupdate_hfree.
  - unfold pt. simpl. destruct (Z.eq_dec x x); auto. exfalso. apply n. auto.
  - admit. (* gg, implication does not mean subheap *)
Abort.

(* Example e31 : forall x,
  entails
    (req any)
    (req (pt x 1)).
Proof.
  intros.
  unfold entails; intros.
  unfold req in H.
  destruct H as [h1 [h2 [H1 [H2 [H3]]]]].
  (* h1 is empty, h2 = t 0 = t 1 *)

  unfold req.
  (* h0 is x->1, h3 is h2-h0 *)
  exists (hupdate x 1 hempty).
  (* pose proof (exists h3, h2 = hunion h4 h3). *)
  exists (hfree x h2).
  repeat split.
  - rewrite H3 in H1.
    rewrite hunion_empty in H1.
    rewrite <- H1.
    pose proof (pt_hunion_hupdate_free _ _ _ H).
    rewrite H4. auto.
  - apply hdisjoint_hupdate_hfree.
  - unfold pt. simpl. destruct (Z.eq_dec x x); auto. exfalso. apply n. auto.
  - admit. (* gg, implication does not mean subheap *)
Abort. *)


End Trace.
