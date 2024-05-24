
From Coq Require Import ZArith Lia Bool List String Program.Equality.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Common Sequences Separation2 Tactics.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** * Syntax *)

Inductive expr : Type :=
  | eint (i:Z)
  | elamb (x:ident) (e:expr)
  | evar (x:ident)
  (* | efree (v:ident) *)
  (* | ebound (i:nat) *)
  (* https://chargueraud.org/research/2009/ln/main.pdf *)
  | eapp (f:ident) (x:ident)
  | elet (x:ident) (e1:expr) (e2:expr)
  | eassert (x:assertion Z) (* no mutual recursion *)
  | eif (x:ident) (e1:expr) (e2:expr)
  | eshift (e:ident)
  | ereset (e:expr).

(** * Model *)

(** Values occur at runtime and may not have a corresponding syntax. *)

Inductive val : Type :=
  | vloc (i:Z)
  | vint (i:Z)
  | vclos (x:ident) (e:expr) (s:store val).

(* Inductive is_val : expr -> Prop :=
  | vint : forall n, is_val (eint n)
  | vlamb : forall x b, is_val (elamb x b). *)

(* Definition to_val (v:expr) : option val :=
  match v with
  | eint i => Some (vint i)
  | elamb x e => Some (vlamb x e)
  | elamb x e => Some (vlamb x e)
  | _ => None. *)

Definition store := store val.
Definition heap := heap val.

Inductive eresult : Type :=
  | resshift (ve:expr) (vl:expr)
  | resbot
  | resnorm (v:val).

(** * Big-step semantics *)

Reserved Notation " 'eval[' s ',' h ',' e ']' '=>' '[' s1 ',' h1 ',' r ']' " (at level 50, left associativity).

Inductive bigstep : store -> heap -> expr -> store -> heap -> eresult -> Prop :=

  | eval_int : forall s h i,
    eval[ s, h, eint i ]=>[ s, h, resnorm (vint i) ]

  | eval_lamb : forall s h x e,
    eval[ s, h, elamb x e ]=>[ s, h, resnorm (vclos x e s) ]

  | eval_var : forall s h x v,
    Some v = s x ->
    eval[ s, h, evar x ]=>[ s, h, resnorm v ]

  | eval_app : forall f x y e v s h s1 h1 r sf,
    Some (vclos y e sf) = s f ->
    Some v = s x ->
    eval[ supdate f (vclos y e sf) (supdate y v sf), h, e ] => [ s1, h1, r ] ->
    eval[ s, h, eapp f x ] => [ s, h1, r ]

  | eval_let : forall x e1 e2 v s h h2 s2 s1 h1 r,
    eval[ s, h, e1 ] => [ s1, h1, resnorm v ] ->
    eval[ supdate x v s1, h1, e2 ] => [ s2, h2, r ] ->
    eval[ s, h, elet x e1 e2 ] => [ sremove x s2, h2, r ]

  | eval_ift : forall x e1 e2 s h s1 h1 r,
    Some (vint 0) = s x ->
    eval[ s, h, e1 ] => [ s1, h1, r ] ->
    eval[ s, h, eif x e1 e2 ] => [ s1, h1, r ]

  | eval_iff : forall x e1 e2 s h s1 h1 r,
    Some (vint 0) <> s x ->
    eval[ s, h, e2 ] => [ s1, h1, r ] ->
    eval[ s, h, eif x e1 e2 ] => [ s1, h1, r ]

  | eval_shift : forall x e b s h y sf,
    Some (vclos x e sf) = s b ->
    eval[ s, h, eshift b ] => [ s, h, resshift (elamb x e) (elamb y (evar y)) ]

  | eval_letshift : forall x e1 e2 s h s1 h1 r el vl z f,
    eval[ s, h, e1 ] => [ s1, h1, resshift el vl ] ->
    r = resshift el (elamb z (elet z (elet f vl (eapp f z)) e2)) ->
    eval[ s, h, elet x e1 e2 ] => [ s1, h1, r ]

  | eval_resetshift : forall e s h s1 h1 s2 h2 r el vl f x,
    eval[ s, h, e ] => [ s1, h1, resshift el vl ] ->
    eval[ s, h, ereset (elet f el (elet x vl (eapp f x))) ] => [ s2, h2, r ] ->
    eval[ s, h, ereset e ] => [ s2, h2, r ]

  | eval_resetval : forall e s h s1 h1 v,
    eval[ s, h, e ] => [ s1, h1, resnorm v ] ->
    eval[ s, h, ereset e ] => [ s1, h1, resnorm v ]

where " 'eval[' s ',' h ',' e ']' '=>' '[' s1 ',' h1 ',' r ']' " := (bigstep s h e s1 h1 r).


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
