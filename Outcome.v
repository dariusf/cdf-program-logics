
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
  Definition rassertion := store -> store -> Prop.
  Definition precond := assertion.
  Definition postcond := val -> rassertion.

  Inductive rea := Term | MayLoop | Loop. (* resource assertion *)
  Inductive lar := LR (d:precond) (r:rea). (* logic and resource *)

  Inductive outcome : Type :=
    | ok_er_nt : postcond -> precond -> precond -> outcome.

  Definition ok_only (q:postcond) : outcome := ok_er_nt q
    (fun _ => False) (fun _ => False).

  (* TODO sl entailment *)
  (* TODO resource entailment *)
  (* TODO case specs *)
  (* TODO disjunction of D|R *)

  (* TODO defn of compose is wrong *)

  (*
    (old(x)=1 /\ x=2) o{x} (old(x)=2 /\ x=3)
    ==> ex u. (old(x)=1 /\ x=2)[x:=u] /\ (old(x)=2 /\ x=3)[old(x):=u]
    ==> ex u. old(x)=1 /\ u=2 /\ u=2 /\ x=3
    ==> ex u. old(x)=1 /\ u=2 /\ x=3
  *)
  (*
    (fun old s => old x=1 /\ s x=2) o{x} (fun old s => old x=2 /\ s x=3)
    ==> ex u. (fun old s => old x=1 /\ s x=2) /\ (fun old s => old x=2 /\ s x=3)
  *)
  (* composition of relational assertions *)
  (* Definition compose u (p1 p2:rassertion) : rassertion :=
    fun old s => p1 old u /\ p2 u s
  . *)
  (* Definition compose (v:ident) (P Q:rassertion) : rassertion := *)
  (* say P is (fun s1 => s1 "x" = 1) *)
    (* fun old s => exists u, P (supdate v u s) /\ Q s *)
    (* TODO this is existential on value, not variable *)
    (* being able to refer to old(v) is a relational assertion *)

  CoInductive diverges : store -> expr -> Prop :=
    | div_pcall : forall e y v s f a s1,
      diverges s1 e ->
      s1 = supdate y v s ->
      fenv f = Some (fn y e) ->
      diverges s (pcall f a)
    .

  Definition triple (P: precond) (e: expr) (Q: outcome) : Prop :=
    forall ok er nt r s s1,
      Q = ok_er_nt ok er nt ->
      P s ->
           (eval[ s, e ] => [ s1, Some r ] -> ok r s s1)
        /\ (eval[ s, e ] => [ s1, None ] -> er s)
        /\ (diverges s e -> nt s).

  Definition aand (P:assertion) (Q:rassertion) : rassertion :=
    fun old s => P old /\ Q old s.

  Lemma f_pconst : forall v p,
    triple p (pconst v) (ok_only (fun r => aand p (fun old s => r = v))).
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

  Lemma f_var : forall x p,
    triple p (pvar x) (ok_only (fun r => aand p (fun old s => Some r = old x))).
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

  (* old(x)=1 /\ x=2 /\ y=4 *)
  (* x=3 *)

  (* ex u. old(x)=1 /\ u=2 /\ x=3 /\ y=4 *)
  (* or *)
  (* old(x)=1 /\ x=3 /\ y=4 *)

  Definition update (p:assertion) (x1 x2:ident) : rassertion :=
      fun old s =>
        forall v2,
        Some v2 = old x2 ->
        p old /\ s = supdate x1 v2 old.

  Example e2 : forall old s x y,
    old y = Some 2 ->
    update (fun s => s x = Some 1) x y old s ->
    (fun old s => old x = Some 1 /\ s x = Some 2) old s.
  Proof.
    intros.
    simpl.
    unfold update in H0.
    symmetry in H.
    specialize (H0 2 H).
    destruct H0.
    split.
    auto.
    rewrite H1.
    now rewrite supdate_same.
  Qed.

  Lemma f_passign : forall x1 x2 p,
    triple p (passign x1 x2) (ok_only (fun _ => update p x1 x2)).
  Proof.
    intros.
    unfold triple.
    intros.
    unfold ok_only in H; injection H; clear H; intros.
    repeat split; intros.
    - rewrite <- H2.
      inversion H3; subst; clear H3.
      unfold update.
      intros.
      split. auto.
      congruence.
    - inversion H3.
    - inversion H3.
  Qed.

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