
From Coq Require Import ZArith Lia Bool List String Program.Equality.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Common Sequences.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* some old tactics *)

(* Tactic Notation "inv" constr(h) := inversion h; subst. *)
Tactic Notation "inj" constr(h) := injection h as h; subst.
Tactic Notation "ok" := auto; try easy.

(* these could be made less powerful in future, so they can't be used wrongly *)
Tactic Notation "vacuous" := easy.
(* Tactic Notation "ih" := ok. *)

Tactic Notation "case_on" constr(e) := let H := fresh in destruct e eqn:H; ok.
Tactic Notation "case_on" constr(e) ident(x) := destruct e eqn:x; ok.
(* Tactic Notation "gen" ident_list(x) := generalize dependent x. *)

(* new ones *)

Ltac inv H := inversion H; clear H; subst.

Module Flow3.

  Definition val := Z.

  Inductive expr : Type :=
    | pvar (x: ident)
    | pconst (n: val)
    | plet (x: ident) (e1: expr) (e2: expr)
    | passign (x1: ident) (x2: ident)
    | pif (x: ident) (e1: expr) (e2: expr)
    | pcall (x: ident) (a: ident)
    .

  Inductive eresult : Type :=
    | enorm : val -> eresult
  .

  Reserved Notation " 'eval[' s ',' e ']' '=>' '[' s1 ',' r ']' " (at level 50, left associativity).

  Inductive bigstep : store -> expr -> store -> eresult -> Prop :=
    | eval_pvar : forall s x,
      eval[ s, pvar x ]=>[ s, enorm (s x)]
    | eval_pconst : forall s x,
      eval[ s, pconst x ] => [ s, enorm x]
    | eval_plet : forall x e1 e2 v s s2 s1 r,
      eval[ s, e1 ] => [ s1, enorm v ] ->
      eval[ supdate x v s1, e2 ] => [ s2, r] ->
      eval[ s, plet x e1 e2 ] => [ s, r ]
    | eval_assign : forall x1 x2 s,
      eval[ s, passign x1 x2 ] => [ s, enorm 0]
      (* TODO call *)
      (* TODO coinductive *)

    where " 'eval[' s ',' e ']' '=>' '[' s1 ',' r ']' " := (bigstep s e s1 r)
  .

  Definition assertion := store -> Prop.
  Definition precond := assertion.
  Definition postcond := val -> assertion.

  Definition aand (P Q: assertion) : assertion :=
    fun s => P s /\ Q s.

  Inductive outcome : Type :=
    | ok_er_nt : postcond -> precond -> precond -> outcome.

  Inductive forward : precond -> expr -> outcome -> Prop :=
    | f_pvar : forall x d,
      forward d (pvar x) (ok_er_nt (fun r => aand d (fun s => r = s x)) d d)
    | f_pconst : forall v d,
      forward d (pconst v) (ok_er_nt (fun r => aand d (fun s => r = v)) d d)
    (* | f_pconst : forall s x,
      eval[ s, pconst x ] => [ s, enorm x]
    | f_plet : forall x e1 e2 v s s2 s1 r,
      eval[ s, e1 ] => [ s1, enorm v ] ->
      eval[ supdate x v s1, e2 ] => [ s2, r] ->
      eval[ s, plet x e1 e2 ] => [ s, r ]
    | f_assign : forall x1 x2 s,
      eval[ s, passign x1 x2 ] => [ s, enorm 0] *)
  .

End Flow3.