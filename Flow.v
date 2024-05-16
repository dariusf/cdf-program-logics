
From Coq Require Import ZArith Lia Bool List String Program.Equality.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Common Sequences Separation2 Tactics.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition val := Z.

Inductive expr : Type :=
  | pvar (x: ident)
  | pconst (n: val)
  | plet (x: ident) (e1: expr) (e2: expr)
  (* | pref (x: ident) *)
  (* | pderef (x: ident) *)
  (* | passign (x1: ident) (x2: ident) *)
  | pif (x: ident) (e1: expr) (e2: expr)
  | pcall (x: ident) (a: ident)
  .

Inductive eresult : Type :=
  | enorm : val -> eresult
.

Reserved Notation " 'eval[' s ',' h ',' e ']' '=>' '[' s1 ',' h1 ',' r ']' " (at level 50, left associativity).

Definition store := store Z.

Inductive bigstep : store -> heap -> expr -> store -> heap -> eresult -> Prop :=
  | eval_pvar : forall s h x v,
    Some v = s x ->
    eval[ s, h, pvar x ]=>[ s, h, enorm v]
  | eval_pconst : forall s h x,
    eval[ s, h, pconst x ] => [ s, h, enorm x]
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

  where " 'eval[' s ',' h ',' e ']' '=>' '[' s1 ',' h1 ',' r ']' " := (bigstep s h e s1 h1 r)
.

Module ProgramExamples.

  (* Example ex_ref :
    eval[ sempty, hempty, plet "x" (pconst 1) (pref "x") ]=>[ sempty, hupdate 2 1 hempty, enorm 2 ].
  Proof.
    apply eval_plet with (v:=1) (s1:=sempty) (s2:=supdate "x" 1 sempty) (h1:=hempty).
    apply eval_pconst.
    apply eval_pref.
    constructor.
  Qed. *)

End ProgramExamples.

Definition precond := assertion.
Definition postcond := Z -> assertion.

Inductive result : Type :=
  | norm : Z -> result.

  Definition compatible r1 r2 :=
    match (r1, r2) with
    | (norm r3, enorm r4) => r3 = r4
  end.

Inductive flow : Type :=
  | req : precond -> flow
  | ens : postcond -> flow
  | seq : flow -> flow -> flow
  (* | fexists : (Z -> flow) -> flow. *)
  | fexists : ident -> flow -> flow.

(* Definition flow := Z -> stages. *)

Infix ";;" := seq (at level 80, right associativity).

Fixpoint replace_ret x f :=
  match f with
  | ens q => ens (fun r s h => exists old v, s x = Some v /\ ((r = v) //\\ q old) s h)
  | req _ => f
  | seq a b => seq a (replace_ret x b)
  | fexists i f => fexists i (replace_ret x f)
  end.

(* Definition replace_ret (x:ident) (f:flow) : flow := fun s1 h1 s2 h2 r =>
  exists v, Some v = s1 x /\
  f s1 h1 s2 h2 (norm v). *)

(* Reserved Notation " 'sem[' t ',' s ',' h ']=>[' t1 ',' s1 ',' h1 ',' r ']' '|=' f " (at level 50, left associativity). *)

(* axiomatization of semantics for staged formulae *)
Inductive satisfies : store -> heap -> store -> heap -> result -> flow -> Prop :=

  | sem_req: forall p s1 h1 s2 h2 r,
    s1 = s2 ->
    (* h3 is the piece taken out satisfying p *)
    (exists h3, h1 = hunion h2 h3 /\ hdisjoint h2 h3 /\ p s1 h3) ->
    satisfies s1 h1 s2 h2 (norm r) (req p)

  | sem_ens: forall q s1 h1 s2 h2 r h3 v,
    s1 = s2 ->
    (* forall v, r = norm v -> *)
    r = norm v /\
    (* h3 is the piece satisfying q that is addded to h1 *)
    h2 = hunion h1 h3 /\ hdisjoint h1 h3 /\ q v s1 h3 ->
    satisfies s1 h1 s2 h3 (norm v) (ens q)

  | sem_seq: forall f1 f2 s1 h1 s2 h2 r s3 h3 r1,
    satisfies s1 h1 s3 h3 r1 f1 ->
    satisfies s3 h3 s2 h2 r f2 ->
    satisfies s1 h1 s2 h2 r (seq f1 f2)

  (* | sem_ex: forall s s1 h1 h2 x e r,
    (* the reason we can't use hoas is that the binding to the existential has to appear in the stack... *)
    (exists v, , supdate x v s, h1]=>[true, s1, h2, r] |= e) ->
    sem[true, s, h1]=>[true, s1, h2, r] |= fun r1 => fexists x (e r1) *)

  | sem_ex: forall x f s1 h1 s2 h2 r,
    s1 x = None ->
    satisfies s1 h1 s2 h2 r (fexists x f)
    (* f (supdate i v s1) h1 s2 h2 r *)
  
    (* sem[true, s1, h1]=>[true, s2, h2, norm r1] |= f1 ->
    sem[true, s2, h2]=>[c, s3, h3, r2] |= f2 ->
    st1 = f1 r1 ->
    st2 = f2 r1 ->
    ff r1 = (st1;;st2) ->
    sem[true, s1, h1]=>[c, s3, h3, r2] |= ff *)


    (* where " 'sem[' t ',' s ',' h ']=>[' t1 ',' s1 ',' h1 ',' r ']' '|=' f " := (satisfies t s h t1 s1 h1 r f) *)
  .


(* Module SemanticsExamples.

  Definition f1 : flow := fun r => ens (fun r1 => pure (r1=1 /\ r=r1)).
  Definition f2 : flow := fun (r:Z) => req (fun s h => s "x" = Some 1).

  (* ex z; req x->z; ens[r] x->1/\r=1 *)
  Definition f3 : flow := fun r =>
    (* fexists "z" (req (pts "x" "z") ;; ens ((r=1) //\\ ptsval "x" 1)). *)
    fexists "z" (req (pts "x" "z") ;; ens (fun r1 => (r=r1) //\\ ptsval "x" 1)).

  Example ex_sem_f1:
    sem[true, sempty, hempty]=>[true, sempty, hempty, norm(1)] |= f1.
  Proof.
    apply sem_ens with (q := fun r => pure (r=1)).
    exists hempty.
    heap.
    unfold pure.
    intuition auto.
    unfold f1.
    f_equal.
    unfold pure.
    apply functional_extensionality.
    intros.
    apply functional_extensionality.
    intros.
    apply functional_extensionality.
    intros.
    auto.
    apply propositional_extensionality.
    intuition auto.
  Qed. *)

  (* Example ex_sem_f3:
    sem[true, (supdate "x" 2 sempty), (hupdate 2 3 hempty) ]=>[
      true, (supdate "x" 2 sempty), (hupdate 2 1 hempty), norm(1)] |= f3.
  Proof.
  (* unfold f3. *)
    apply sem_ex.
    exists 1.
  (* Unset Printing Notations. *)
    apply sem_seq with (f1 := fun r => req (pts "x" "z"))
      (f2 := fun r => ens (ptsval "x" 1))
      (r1 := 1)
      (h2 := hempty)
      (s2 := (supdate "x" 2 sempty))
    .
    - apply sem_req.
    exists (hupdate 2 3 hempty).
    heap.
    unfold pts.
    unfold contains.
    unfold supdate. simpl.
    admit.
    -
    unfold pureconj.
    apply sem_ens.
    admit.
    - auto.
  Admitted. *)
  (* Qed. *)

(* End SemanticsExamples. *)


(* forward rules say how to produce a staged formula from a program *)
Inductive forward : expr -> flow -> Prop :=
  | fw_const: forall n,
    forward (pconst n) (ens (fun res => (res = n) //\\ emp))

  | fw_var: forall x v,
    forward (pvar x) (ens (fun res s h => s x = Some v /\ res = v /\ emp s h))

  (* | fw_deref: forall x y,
    forward (pderef x) (fexists y (req (pts x y);;
      ens (fun res s h => ((res = s y) //\\ pts x y) s h)))

  | fw_ref: forall x y,
    (* forward (pref x) (fexists (fun y => ens (fun r s h => contains y (s x) s h))) *)
    forward (pref x) (fexists y (ens (fun r s h => (r = s y) /\ (pts y x s h)))) *)

  | fw_let: forall x e1 e2 f1 f2 f3,
    forward e1 f1 ->
    forward e2 f2 ->
    replace_ret x f1 = f3 ->
    forward (plet x e1 e2) (fexists x (f3 ;; f2))

  (* | fw_get: forall l v, 
    forward (GET l)
      (req (contains l v) ;;
      (ens (fun r => (r = v) //\\ contains l v))) *)
.

(** The semantics only grows the store *)
Definition wellformed (f:flow) s1 h1 s2 h2 r :=
  satisfies s1 h1 s2 h2 r f -> substore s1 s2.
  (* f s1 h1 s2 h2 r -> substore s1 s2. *)

(** Replacing the return value preserves wellformedness *)
(* Lemma replace_ret_wellformed : forall f x s1 h1 s2 h2 v v1,
  Some v = s1 x ->
  wellformed f s1 h1 s2 h2 (norm v) ->
  wellformed (replace_ret x f) s1 h1 s2 h2 (norm v1).
Proof.
  intros f.
  induction f; intros x s1 h1 s2 h2 v v1 H.
  (* unfold wellformed. *)
  (* intros Hs. *)
  (* unfold satisfies in H1. *)
  (* inv H1. *)
  (* induction f; inv Hs; destr_all. *)
  - unfold wellformed.
  intros Hs H1.
  apply Hs.
  simpl in H1.
  auto. *)


(* - unfolds. intros. unfolds in Hs. apply Hs. simpl in H0. auto. *)

(* 
  
  - unfolds. intros.
    unfolds in Hs. apply Hs. clear Hs.
    simpl in H0.
    inv H0.
    (* destr_all. *)
    unfolds in H7.
    (* destr_all. *)
    subst.
    Print sem_ens.
    apply sem_ens with (r:=norm H4) (h2:=hunion h1 h2).
    auto.
    eapply H0. *)



    (* heap. *)
    (* constructor. *)
  (* -
  apply IHf2.
  unfolds.
  intros.
  apply IHf1.
  unfolds.
  intros.
  
  unfolds in H0.
  apply H0.
  eapply sem_seq with (s3:=s4) (h3:=h4).
  exact H8.

  auto.
  auto.
  admit.
  - admit. *)
  (* Abort. *)
(* Qed. *)
