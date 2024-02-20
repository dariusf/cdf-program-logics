
From Coq Require Import ZArith Lia Bool List String Program.Equality.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Sequences Separation Seplog.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Module Flow3.

Inductive flow : Type :=
| req : precond -> flow
| ens : postcond -> flow
| seq : flow -> flow -> flow
.

Infix ";;" := seq (at level 80, right associativity).

Inductive satisfies : heap -> heap -> flow -> Prop :=
  | sem_req: forall h3 p h1,
    (exists h2, h3 = hunion h1 h2 /\ hdisjoint h1 h2 /\ p h2) ->
    satisfies h3 h1 (req p)
  | sem_ens: forall h1 h2 h3 q v,
    h3 = hunion h1 h2 -> hdisjoint h1 h2 ->
    q v h2 ->
    satisfies h1 h3 (ens q)
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

Theorem soundness : forall f c1 h1 h2 h3,
  satisfies h1 h3 f ->
  forward c1 f ->
  terminates c1 h1 h2 ->
  h2 = h3.
Proof.
  intros f c1 h1 h2 h3 Hs.
  induction Hs; intros Hf Ht.
  - inv Hf.
  - { inv Hf.
    - { inv Ht.
      admit.
    }
    (* - inv Ht. inv H0. inv H1. inv H2. inv H. inv H1. inv H0. rewrite hunion_comm. rewrite hunion_empty. auto. *)
    (* HDISJ. inv H0. *)
    - admit.
  }
Admitted.
(* Qed. *)


End Flow3.