
From Coq Require Import ZArith Lia Bool List String Program.Equality.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Common Sequences.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition val := Z.

Inductive expr : Type :=
  | pvar (x: ident)
  | pconst (n: val)
  | plet (x: ident) (e1: expr) (e2: expr)
  | passign (x1: ident) (x2: ident)
  | pif (x: ident) (e1: expr) (e2: expr)
  | pcall (x: ident) (a: ident)
  .

(* Inductive eresult : Type :=
  | enorm : val -> eresult
  . *)
Definition eresult := option val.

Inductive fndef : Type := fn (i:ident) (b:expr).
Definition fnenv : Type := ident -> option fndef.
Definition fnenv_empty : fnenv := (fun _ => None).
Definition fupdate (x: ident) (v: fndef) (s: fnenv) : fnenv :=
  fun y => if string_dec x y then Some v else s y.

Section Bigstep.

  Variable fenv : fnenv.

  Reserved Notation " 'eval[' s ',' e ']' '=>' '[' s1 ',' r ']' " (at level 50, left associativity).

  CoInductive bigstep : store -> expr -> store -> eresult -> Prop :=

    | eval_pvar : forall s x r,
      s x = Some r ->
      eval[ s, pvar x ]=>[ s, Some r ]

    | eval_pconst : forall s x,
      eval[ s, pconst x ] => [ s, Some x ]

    | eval_plet : forall x e1 e2 v s s2 s1 r,
      eval[ s, e1 ] => [ s1, Some v ] ->
      eval[ supdate x v s1, e2 ] => [ s2, r] ->
      eval[ s, plet x e1 e2 ] => [ s, r ]

    | eval_pif_t : forall x e1 e2 s s1 r,
      eval[ s, e1 ] => [ s1, r ] ->
      s x = Some 0 ->
      eval[ s, pif x e1 e2 ] => [ s1, r ]

    | eval_pif_f : forall x e1 e2 s s1 r,
      eval[ s, e2 ] => [ s1, r ] ->
      s x <> Some 0 ->
      eval[ s, pif x e1 e2 ] => [ s1, r ]

    | eval_pcall : forall a f e s s1 r v y,
      eval[ supdate y v s, e ] => [ s1, r ] ->
      s a = Some v ->
      fenv f = Some (fn y e) ->
      eval[ s, pcall f a ] => [ s1, r ]

    | eval_passign : forall x1 x2 s v s1,
      s x2 = Some v ->
      s1 = supdate x1 v s ->
      eval[ s, passign x1 x2 ] => [ s1, Some 0 ]

  where " 'eval[' s ',' e ']' '=>' '[' s1 ',' r ']' " := (bigstep s e s1 r)
  .

  Example e1 : forall x1 x2 s,
    s = supdate x2 1 (supdate x1 0 sempty) ->
    eval[ s, passign x1 x2 ] =>
      [ supdate x1 1 s, Some 0 ].
  Proof.
    intros.
    apply eval_passign with (v := 1).
    2: reflexivity.
    rewrite H; now rewrite supdate_same.
  Qed.

  Inductive nati := n (n:nat) | inf.
  Inductive resources := rb (l:nati) (u:nati).
  Definition model := store -> resources -> Prop.

  Definition assertion := store -> Prop.
  Definition precond := assertion.
  Definition postcond := val -> assertion.

  Definition aand (P Q: assertion) : assertion :=
    fun s => P s /\ Q s.

  Inductive rea := Term | MayLoop | Loop. (* resource assertion *)
  Inductive lar := LR (d:precond) (r:rea). (* logic and resource *)

  Inductive outcome : Type :=
    | ok_er_nt : postcond -> precond -> precond -> outcome.

  Definition ok_only (q:postcond) : outcome := ok_er_nt q (fun _ => False) (fun _ => False).

  (* TODO sl entailment *)
  (* TODO resource entailment *)
  (* TODO case specs *)
  (* TODO disjunction of D|R *)

  (* TODO defn of compose is wrong *)

  Definition compose (v:ident) (P Q:assertion) : assertion :=
  (* say P is (fun s1 => s1 "x" = 1) *)
    fun s => exists u, P (supdate v u s) /\ Q s
    (* TODO this is existential on value, not variable *)
    (* being able to refer to old(v) is a relational assertion *)
  .

  CoInductive diverges : store -> expr -> Prop :=
    | div_pcall : forall e y v s f a s1,
      diverges s1 e ->
      s1 = supdate y v s ->
      fenv f = Some (fn y e) ->
      diverges s (pcall f a)
    .

  Definition triple (P: precond) (e: expr) (Q: outcome) : Prop :=
    forall ok er nt r s s1, Q = ok_er_nt ok er nt ->
      P s ->
          (eval[ s, e ] => [ s1, Some r ] -> ok r s1)
        /\ (eval[ s, e ] => [ s1, None ] -> er s)
        /\ (diverges s e -> nt s).

  Lemma f_pconst : forall v p,
    triple p (pconst v) (ok_only (fun r => aand p (fun s => r = v))).
  Proof.
    intros.
    unfold triple.
    intros.
    unfold ok_only in H; injection H; clear H; intros.
    repeat split; intros.
    - inversion H3; subst; clear H3.
      unfold aand; easy.
    - inversion H3.
    - inversion H3.
  Qed.

  Lemma f_passign : forall x1 x2 p,
    triple p (passign x1 x2) (ok_only (fun _ => compose x1 p (fun s => s x1 = s x2))).
  Proof.
    intros.
    unfold triple.
    intros.
    unfold ok_only in H; injection H; clear H; intros.
    repeat split; intros.
    - rewrite <- H2.
      inversion H3; subst.
      unfold compose.
      exists v.
      inversion H3; subst; clear H3.
      split.
      (* pose ident. *)
      (* exists r. *)
      admit.
      rewrite H6.
      f_equal.
      admit.
    - inversion H3.
    - inversion H3.
  Admitted.
  (* Qed. *)

  (* Inductive forward : precond -> expr -> outcome -> Prop :=

    | f_pvar : forall x s,
      forward s (pvar x) (ok_only (fun r => aand s (fun s => Some r = s x)))

    | f_pconst : forall c s,
      forward s (pconst c) (ok_only (fun r => aand s (fun s => r = c)))

    | f_passign : forall x1 x2 s,
      forward s (passign x1 x2) (ok_only (fun _ => compose x1 s (fun s => s x1 = s x2)))
      (*
        S o{v} (v=x)
        ==> ex u. S[v:=u] /\ (v=x)[old(v):=u]
        ==> ex u. S[v:=u] /\ v=x
      *)
. *)

  (* Example e2 : forall x1 x2 s,
    (* st = supdate x2 1 (supdate x1 0 sempty) -> *)
    forward s (passign x1 x2) (ok_only (fun _ => fun s => s x1 = s x2)).
  Proof.
    intros.
    constructor.
  Qed. *)

    (* TODO if *)
    (* | f_pif : forall c s x e1 e2,
      forward s (pif x e1 e2) (ok_only (fun r => aand s (fun s => r = c))) *)

    (* TODO let *)

    (* TODO call *)
    (* | f_pcall : forall y b f c r x d,
      fenv f = Some (fn y b) ->
      forward (LR d r) (pcall f x) (ok_only (fun r => aand s (fun s => r = c))) *)
  
End Bigstep.