
From Coq Require Import ZArith Lia Bool List String Program.Equality.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Sequences Separation Seplog.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Ltac HUNION :=
  match goal with
  | [ |- _ = hunion hempty _ ] =>
      rewrite hunion_empty; HUNION
  | [ |- _ = hunion _ hempty ] =>
      rewrite hunion_comm; rewrite hunion_empty; HUNION
  | _ => auto
  end.

Ltac heap := HUNION; HDISJ; auto.

Module Flow3.

Inductive flow : Type :=
| req : precond -> flow
| ens : postcond -> flow
| seq : flow -> flow -> flow
.

Infix ";;" := seq (at level 80, right associativity).

Inductive result : Type :=
| norm : Z -> result
(* | eff : postcond -> flow *)
.

Inductive satisfies : bool -> heap -> bool -> heap -> result -> flow -> Prop :=
  | sem_req: forall h3 p h1 r,
    (exists h2, h3 = hunion h1 h2 /\ hdisjoint h1 h2 /\ p h2) ->
    satisfies true h3 true h1 (norm r) (req p)
  | sem_ens: forall h1 h2 h3 q v,
    h3 = hunion h1 h2 -> hdisjoint h1 h2 ->
    q v h2 ->
    satisfies true h1 true h3 (norm v) (ens q)
  | sem_seq: forall f1 f2 r r1 h1 h2 h3 c,
    satisfies true h1 true h2 r f1 ->
    satisfies true h2 c h3 r1 f2 ->
    satisfies true h1 c h3 r1 (f1;;f2)
.

(* forward rules. says how to produce a flow from a program *)
Inductive forward : com -> flow -> Prop :=
  | fw_skip:
    forward SKIP (ens (fun v h => True))
  | fw_pure: forall n,
    forward (PURE n) (ens (fun res => pure (res = n)))
  | fw_get: forall l v, 
    forward (GET l)
      (req (contains l v) ;;
      (ens (fun r => (r = v) //\\ contains l v)))
.

Definition terminated (c: com) : Prop :=  c = SKIP.

Definition terminates (c1: com) (h1 h2: heap) : Prop :=
  exists c2, star red (c1, h1) (c2, h2) /\ terminated c2.

Theorem soundness : forall f e1 h1 h2 h3 c r,
  satisfies true h1 c h3 r f ->
  forward e1 f ->
  terminates e1 h1 h2 ->
  h2 = h3.
Proof.
(* Abort. *)
Proof.
  intros f e1 h1 h2 h3 c r Hs.
  induction Hs; intros Hf Ht.
  - inv Hf.
  - { inv Hf.
    - {
      inv Ht.
      admit.
    }
    (* - inv Ht. inv H0. inv H1. inv H2. inv H. inv H1. inv H0. rewrite hunion_comm. rewrite hunion_empty. auto. *)
    (* HDISJ. inv H0. *)
    - admit.
  }
Admitted.
(* Qed. *)

Example ex_spec_return_anything: exists x,
  satisfies true hempty true hempty (norm x) (req emp).
Proof.
  exists 1.
  constructor.
  auto.
  exists hempty.
  repeat split; heap.
Qed.

Example ex_spec_ens_1:
  satisfies true hempty true hempty (norm 1) (ens (fun r => (r = 1) //\\ emp)).
Proof.
  apply sem_ens with (h2 := hempty).
  heap.
  heap.
  split.
  auto. constructor.
Qed.

Example ex_spec_seq: forall x,
  satisfies true (hupdate x 1 hempty) true (hupdate x 1 hempty) (norm 2)
  (req (contains x 1);; ens (fun r => (r = 2) //\\ contains x 1)).
Proof.
  intros.
  apply sem_seq with (h2 := hempty) (r := norm 3).
  - constructor.
  exists (hupdate x 1 hempty).
  repeat split.
  heap.
  heap.
  - apply sem_ens with (h2 := hupdate x 1 hempty).
  heap.
  heap.
  split.
  auto.
  unfold contains.
  reflexivity.
Qed.

End Flow3.