
From Coq Require Import ZArith Lia Bool List String Program.Equality.
Local Open Scope Z_scope.

Local Open Scope string_scope.
  Definition ident := string.
  Definition store : Type := ident -> Z.
  Definition sempty : store := (fun _ => 0).
  Definition supdate (x: ident) (v: Z) (s: store) : store :=
    fun y => if string_dec x y then v else s y.
