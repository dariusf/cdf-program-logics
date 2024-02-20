
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
      rewrite hunion_empty; idtac 1; HUNION
  | [ |- _ = hunion _ hempty ] =>
      idtac 4; rewrite hunion_comm;
      HUNION
      (* rewrite hunion_empty; idtac 2; HUNION *)
  | _ => idtac 3; auto
  end.

Ltac heap := HUNION; HDISJ; auto.

(* Ltac rw := rewrite. *)
(* Ltac con := constructor. *)

Ltac destr H :=
  match type of H with
  | ex _ =>
    let L := fresh "e" in
    let R := fresh "H" in
    destruct H as [L R]; destr R
  | _ /\ _ =>
    let L := fresh "L" in
    let R := fresh "R" in
    destruct H as [L R]; destr L; destr R
  | _ => idtac
  end.

Module Flow3.

Inductive flow : Type :=
| req : precond -> flow
| ens : postcond -> flow
| seq : flow -> flow -> flow
.

Infix ";;" := seq (at level 80, right associativity).

Inductive result : Type :=
| norm : Z -> result
.

(* axiomatization of semantics for staged formulae *)
Inductive satisfies : bool -> heap -> bool -> heap -> result -> flow -> Prop :=
  | sem_req: forall h3 p h1 r,
    (exists h2, h3 = hunion h1 h2 /\ hdisjoint h1 h2 /\ p h2) ->
    satisfies true h3 true h1 (norm r) (req p)
  | sem_ens: forall h1 h3 q v,
    (exists h2, h3 = hunion h1 h2 /\ hdisjoint h1 h2 /\
    q v h2) ->
    satisfies true h1 true h3 (norm v) (ens q)
  | sem_seq: forall f1 f2 r r1 h1 h2 h3 c,
    satisfies true h1 true h2 r f1 ->
    satisfies true h2 c h3 r1 f2 ->
    satisfies true h1 c h3 r1 (f1;;f2)
.

(* forward rules say how to produce a staged formula from a program *)
Inductive forward : com -> flow -> Prop :=
  | fw_skip:
    forward SKIP (ens (fun res => (res = 0) //\\ emp))
  | fw_pure: forall n,
    forward (PURE n) (ens (fun res => (res = n) //\\ emp))
  | fw_get: forall l v, 
    forward (GET l)
      (req (contains l v) ;;
      (ens (fun r => (r = v) //\\ contains l v)))
.

Definition terminated (c: com) : Prop :=  c = SKIP.

Definition terminates (c1: com) (h1 h2: heap) : Prop :=
  exists c2, star red (c1, h1) (c2, h2) /\ terminated c2.

Theorem soundness : forall h1 c h3 r f,
  satisfies true h1 c h3 r f ->
  forall e1 h2,
  forward e1 f ->
  terminates e1 h1 h2 ->
  h2 = h3.
Proof.
  intros h1 c h3 r f Hs.
  induction Hs; intros e1 h0 Hf Ht.
  - inv Hf.
  - { inv Hf.
    (* both ways to produce an ens: skip and pure *)
    - inv Ht.
      inv H.
      destr H1. destruct R0. unfold emp in H1. inv H0.
      (* skip has terminated *)
      { inv H2.
      - heap.
      - inv H.
      }
    - inv Ht. destr H. destr H0.
      { inv L1.
      - destruct R0. unfold emp in H0. subst. heap.
      - inv H. 
      }
  }
  - inv Hf.
  (* only one case for forward rules that produces a seq, which is get *)
  inv Ht.
  destr H.
  (* see how get reduces *)
  { inv L.
  - inv R. (* get does reduce *)
  - inv H.
    { inv H0.
    - inv R.
      (* h0 -> h2 -> h3 *)
      inv Hs1. destr H0. inv Hs2. destr H0. subst.
      unfold contains in R0.
      destruct R1.
      unfold contains in H0.
      subst.
      reflexivity.
    - inv H.
    }
  }
(* Admitted. *)
Qed.

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
  apply sem_ens.
  exists hempty.
  repeat split; heap.
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
  - apply sem_ens.
  exists (hupdate x 1 hempty).
  repeat split; heap.
Qed.

End Flow3.