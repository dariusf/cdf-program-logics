
From Coq Require Import ZArith Lia Bool List String Program.Equality.
From CDF Require Import Common Sequences Separation2 Tactics HeapTactics.

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

Definition empty := ens (fun r => pure True).

Infix ";;" := seq (at level 80, right associativity).

Fixpoint replace_ret x f :=
  match f with
  | ens q => ens (fun _ s h => exists v, s x = Some v /\ q v s h)
  | req _ => f
  | seq a b => seq a (replace_ret x b)
  | fexists i f => fexists i (replace_ret x f)
  end.

Definition compose (x:ident) (f1 f2:flow) : flow :=
  fexists x (replace_ret x f1 ;; f2).

(* Definition replace_ret (x:ident) (f:flow) : flow := fun s1 h1 s2 h2 r =>
  exists v, Some v = s1 x /\
  f s1 h1 s2 h2 (norm v). *)

(* Reserved Notation " 'sem[' t ',' s ',' h ']=>[' t1 ',' s1 ',' h1 ',' r ']' '|=' f " (at level 50, left associativity). *)

(* axiomatization of semantics for staged formulae *)
Inductive satisfies : store -> heap -> store -> heap -> result -> flow -> Prop :=

  | sat_req p s1 h1 s2 h2 r h3
    (Hsu: s1 = s2)
    (* h3 is the piece taken out satisfying p *)
    (Hex: h1 = hunion h2 h3)
    (Hd: hdisjoint h2 h3)
    (Hp: p s1 h3) :
    satisfies s1 h1 s2 h2 (norm r) (req p)

  | sat_ens q s1 h1 s2 h2 h3 v
    (Hsu:s1 = s2)
    (* forall v, r = norm v -> *)
    (* (Hr: r = norm v) *)
    (* h3 is the piece satisfying q that is addded to h1 *)
    (Hh: h2 = hunion h1 h3)
    (Hd: hdisjoint h1 h3)
    (Hq: q v s1 h3) :
    satisfies s1 h1 s2 h2 (norm v) (ens q)

  | sat_seq f1 f2 s1 h1 s2 h2 r s3 h3 r1
    (Hs1: satisfies s1 h1 s3 h3 r1 f1)
    (Hs2: satisfies s3 h3 s2 h2 r f2) :
    satisfies s1 h1 s2 h2 r (seq f1 f2)

  | sat_ex
    x f s1 h1 s2 h2 r
    (Hnotin: s1 x = None)
    (Hex: exists v, satisfies (supdate x v s1) h1 s2 h2 r f) :
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

(** Result can be anything if unconstrained *)
Lemma unconstrained_res : forall s h v,
  satisfies s h s h (norm v) empty.
Proof.
  intros.
  apply sat_ens with (h3:=hempty); heap.
  unfold pure.
  auto.
Qed.

(** replace_ret removes the result value and constrains the given variable *)
Example e_replace_ret : forall x s h,
  satisfies s h s h (norm 2) (replace_ret x (ens (fun r => pure (r = 1)))) <->
    satisfies s h s h (norm 2) (ens (fun r s h => s x = Some 1)).
Proof.
  split.
  - intros.
    simpl in H.
    inv H.
    destr_all.
    unfold pure in H2.
    destr H2.
    subst.
    apply sat_ens with (h3:=hempty); auto.
  - intros.
    simpl.
    inv H.
    apply sat_ens with (h3:=hempty); heap.
    exists 1.
    intuition easy.
Qed.

Module SemanticsExamples.

  (* ex z; req x->z; ens[r] x->1/\r=1 *)
  Definition f3 : flow :=
    fexists "z" (req (pts "x" "z") ;; ens (fun r => (r=1) //\\ ptsval "x" 1)).

  Example ex_sem_f3:
    satisfies (supdate "x" 2 sempty) (hupdate 2 3 hempty)
      (supdate "z" 3 (supdate "x" 2 sempty)) (hupdate 2 1 hempty) (norm 1) f3.
  Proof.
    unfold f3.
    apply sat_ex.
    heap.
    exists 3.
    apply sat_seq with (s3:=supdate "z" 3 (supdate "x" 2 sempty)) (h3:=hempty) (r1:=norm 5).
    - apply sat_req with (h3:=hupdate 2 3 hempty).
      reflexivity.
      heap.
      heap.
      unfold pts.
      exists 2.
      exists 3.
      intuition easy.
    - apply sat_ens with (h3:=hupdate 2 1 hempty); heap.
      (* rewrite supdate_dupe. *)
      (* reflexivity. *)
      unfold pureconj.
      unfold ptsval.
      intuition.
      exists 2.
      intuition.
      unfold contains.
      heap.
  Qed.

End SemanticsExamples.


(* forward rules say how to produce a staged formula from a program *)
Inductive forward : expr -> flow -> Prop :=
  | fw_const: forall n p,
    p = (ens (fun res => (res = n) //\\ emp)) ->
    forward (pconst n) p

  | fw_var: forall x p,
    p = (ens (fun res s h => exists v, s x = Some v /\ res = v /\ emp s h)) ->
    forward (pvar x) p

  (* | fw_deref: forall x y,
    forward (pderef x) (fexists y (req (pts x y);;
      ens (fun res s h => ((res = s y) //\\ pts x y) s h)))

  | fw_ref: forall x y,
    (* forward (pref x) (fexists (fun y => ens (fun r s h => contains y (s x) s h))) *)
    forward (pref x) (fexists y (ens (fun r s h => (r = s y) /\ (pts y x s h)))) *)

  | fw_let: forall x e1 e2 f1 f2,
    forward e1 f1 ->
    forward e2 f2 ->
    (* replace_ret x f1 = f3 -> *)
    (* f1 ;; ens (fun _ => ) = f3 -> *)
    (* forward (plet x e1 e2) (fexists x (f3 ;; f2)) *)
    forward (plet x e1 e2) (compose x f1 f2)

  (* | fw_get: forall l v, 
    forward (GET l)
      (req (contains l v) ;;
      (ens (fun r => (r = v) //\\ contains l v))) *)
.

Example e_fw_let : forall x,
  forward (plet x (pconst 1) (pvar x)) (fexists x (
    replace_ret x (ens (fun r => pure (r=1))) ;;
    ens (fun res s h => exists v, Some v = s x /\ res = v /\ emp s h)
    )).
Proof.
  simpl.
  intros.
  apply fw_let with (f1 := (ens (fun r => pure (r=1)))).
  - eapply fw_const.
    reflexivity.
  - apply fw_var.
    (* trivial from here, but we have to go through this whole song and dance *)
    f_equal.
    post_ext.
    split; intros.
    + destr H.
      intuition.
      exists H0.
      intuition auto.
    + destr H.
      exists H0.
      intuition auto.
Qed.

(** The semantics only grows the store. *)
Definition satisfies_monotonic : forall f s1 h1 s2 h2 r,
  satisfies s1 h1 s2 h2 r f -> substore s1 s2.
Proof.
  induction f; intros.
  - inv H. ok.
  - inv H. ok.
  - inv H.
    specialize (IHf1 _ _ _ _ _ Hs1).
    specialize (IHf2 _ _ _ _ _ Hs2).
    apply substore_trans with (s2 := s4); auto.
  - inv H.
    destruct Hex as [v Hsat].
    specialize (IHf _ _ _ _ _ Hsat).
    specialize (substore_reduce_left _ _ _ _ _ Hnotin IHf).
    ok.
Qed.

Theorem soundness :
  forall se1 he1 e se2 he2 re (**) f ss1 hs1 ss2 hs2 rs,
    bigstep se1 he1 e se2 he2 re ->
    substore se1 ss1 ->
    (* he1 = hs1 -> *)
    forward e f ->
    satisfies ss1 hs1 ss2 hs2 rs f ->
    substore se2 ss2
    (* /\ he2 = hs2 *)
    /\ compatible rs re.
Proof.
  intros se1 he1 e se2 he2 re
          f ss1 hs1 ss2 hs2 rs
          Hb.
  revert f ss1 hs1 ss2 hs2 rs.
  induction Hb;
  intros f ss1 hs1 ss2 hs2 rs;
  intros Hsub Hf Hs.
  - (* var. the proof comes down to the fact that both spec and program read
        s(x) and leave the heap unchanged. *)
    inv Hf.
    inv Hs.
    destr_all; subst.
    intuition.
    unfold compatible.
    unfold emp in H4.
    subst.
    unfold substore in Hsub.
    symmetry in H.
    specialize (Hsub v x H).
    congruence.
  - inv Hf.
    inv Hs.
    destr_all; subst.
    unfold pureconj in Hq.
    destr_all; subst.
    unfold compatible.
    intuition auto.
  -
  (* we have an IH for each subexpr *)
  (* v is the intermediate result of evaluating e1 *)
  (* r is the final result *)
  inv Hf.
  (* the spec is of the form ex x. f1[x/r];f2 *)
  (* see how it evaluates *)
  inv Hs.
  destruct Hex as [v1 Hseq].
  (* v1 is the return value of f1, which can be anything due to replace ret *)
  inv Hseq.

  assert (
    forall x v1 ss1 hs1 s4 h4 r1 f1,
      satisfies (supdate x v1 ss1) hs1 s4 h4 r1 (replace_ret x f1) ->
      satisfies ss1 hs1 s4 h4 (norm v1) f1). admit.
  specialize (H x v1 ss1 hs1 s4 h4 r1 f1 Hs1).
  specialize (IHHb1 f1 ss1 hs1 s4 h4 (norm v1) Hsub H3 H).
  destruct IHHb1 as [Hst Hcomp].

  (* specialize (IHHb2 f2 (supdate x v s1) h4 ss2 hs2 rs). *)
  specialize (IHHb2 f2 s4 h4 ss2 hs2 rs).
  forward IHHb2 by admit.

  assert (s4 x = Some v).
  admit.
  (* from wellformed *)
  assert (s4 = supdate x v s4). admit.
  rewrite H1 in Hs2.
  assert (substore (supdate x v s4) (supdate x v1 ss2)). admit.
  assert (substore s4 ss2). admit.
  assert (satisfies s4 h4 ss2 hs2 rs f2) as Hs3. admit.

  specialize (IHHb2 H4 Hs3).
  intuition.
Admitted.