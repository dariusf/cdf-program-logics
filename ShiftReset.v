
From Coq Require Import ZArith Lia Bool List String Program.Equality.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Common Sequences Separation2 Tactics.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Inductive expr : Set :=
  | eint : Z -> expr
  | elamb : (ident -> expr) -> expr
  | evar : ident -> expr
  | elet : ident -> expr -> expr
  | eif : ident -> expr -> expr
  | eapp : ident -> expr.

Module Values.
  Definition t := expr.
End Values.
Module Store := MakeStore (Values).
Import Store.

Inductive is_val : expr -> Prop :=
  | vint : forall n, is_val (eint n)
  | vlamb : forall b, is_val (elamb b).

Inductive eresult : Type :=
  | resshift : eresult (* TODO *)
  | resbot : eresult
  | resnorm : expr -> eresult.

Reserved Notation " 'eval[' s ',' h ',' e ']' '=>' '[' s1 ',' h1 ',' r ']' " (at level 50, left associativity).

(* Inductive bigstep : forall v, store -> heap -> expr -> store -> heap -> eresult -> Prop :=
  | eval_var : forall s h x v,
    Some v = s x ->
    eval[ s, h, evar x ]=>[ s, h, resnorm v]
  (* | eval_const : forall s h x,
    eval[ s, h, pconst x ] => [ s, h, enorm x] *)
  | eval_plet : forall x e1 e2 v s h h2 s2 s1 h1 r,
    eval[ s, h, e1 ] => [ s1, h1, enorm v] ->
    eval[ supdate x v s1, h1, e2 ] => [ s2, h2, r] ->
    eval[ s, h, plet x e1 e2 ] => [ s2, h2, r ]
  (* | eval_pref : forall x s (h:heap) l,
    h l = None ->
    eval[ s, h, pref x ] => [ s, hupdate l (s x) h, enorm l]
  | eval_deref : forall x s (h:heap) v,
    h (s x) = Some v ->
    eval[ s, h, pderef x ] => [ s, h, enorm v]
  | eval_assign : forall x1 x2 s h,
    eval[ s, h, passign x1 x2 ] => [ s, hupdate (s x1) (s x2) h, enorm 0] *)

where " 'eval[' s ',' h ',' e ']' '=>' '[' s1 ',' h1 ',' r ']' " := (bigstep s h e s1 h1 r). *)


Section ProgramExamples.

  (* Example ex_ref :
    eval[ sempty, hempty, plet "x" (pconst 1) (pref "x") ]=>[ sempty, hupdate 2 1 hempty, enorm 2 ].
  Proof.
    apply eval_plet with (v:=1) (s1:=sempty) (s2:=supdate "x" 1 sempty) (h1:=hempty).
    apply eval_pconst.
    apply eval_pref.
    constructor.
  Qed. *)

End ProgramExamples.
