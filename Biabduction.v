
From Coq Require Import ZArith Lia Bool List String Program.Equality.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Common Sequences Separation2 Tactics.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* like the member predicate. or modulo equivalence? *)
Inductive split : assertion -> assertion -> assertion -> Prop :=
  | split_one : forall h2 x y,
    split (pts x y ** h2) (pts x y) h2

  | split_next : forall h2 x y h h1,
    split h1 h h2 ->
    split (pts x y ** h2) h h2
.

Inductive biab : assertion -> assertion -> assertion -> Prop :=

  | biab_base : forall s m,
    biab s m (pure True)

  | biab_missing : forall x y a m,
    biab emp ((pts x y) ** m) ((pts x y) ** a)

  | biab_match : forall x y z a b m m1,
    biab b m a ->
    (z = y) //\\ m = m1 ->
    biab ((pts x z) ** b) m1 ((pts x y) ** a)
.

Example ex1 : forall x y a b,
  biab (pts x y ** emp) (pts a b) (pts x y ** pts a b).
Proof.
  intros.
  apply biab_match with (m := pts a b).
  (* apply biab_missing with (m := pts a b). *)
Admitted.