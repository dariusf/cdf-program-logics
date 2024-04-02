
From Coq Require Import ZArith Lia Bool List String Program.Equality.
Local Open Scope Z_scope.

Local Open Scope string_scope.

Definition ident := string.
Definition store : Type := ident -> option Z.
Definition sempty : store := (fun _ => None).
Definition supdate (x: ident) (v: Z) (s: store) : store :=
  fun y => if string_dec x y then Some v else s y.

Lemma supdate_same: forall l v h, (supdate l v h) l = Some v.
Proof.
  intros; cbn.
  unfold supdate.
  destruct (string_dec l l); congruence.
Qed.

Lemma supdate_other: forall l v h l', l <> l' -> (supdate l v h) l' = h l'.
Proof.
  intros; cbn.
  unfold supdate.
  destruct (string_dec l l'); congruence.
Qed.

(* s1 <= s2 *)
Definition substore (s1 s2 : store) :=
  forall v x, s1 x = Some v -> s2 x = Some v.
