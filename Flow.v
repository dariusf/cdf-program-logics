
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

(* Lemma sat_req_inv : forall s1 h1 s2 h2 r p,
  satisfies s1 h1 s2 h2 r (req p) ->
  s1 = s2.
Proof.
  intros.
  inv H.
  ok.
Qed. *)



(* p cannot concern x *)
(* Lemma pre_store_extension : forall (p:precond) s1 h s2 x v,
  s1 x = None ->
  p s1 h ->
  s2 = supdate x v s1 ->
  p s2 h.
Proof.
  intros. *)

(* Abort. *)
(* Admitted. *)
(* Qed. *)

(* Lemma sat_store_extension : forall f s1 h1 s2 h2 r s3 s4 x v,
  satisfies s1 h1 s2 h2 r f ->
  substore s1 s2 -> (* wf *)
  substore s3 s4 -> (* wf *)
  (* substore s1 s3 -> *)
  (* substore s2 s4 -> *)
  s3 = supdate x v s1 ->
  s4 = supdate x v s2 ->
  satisfies s3 h1 s4 h2 r f.
Proof.
  (* intros f s1 h1 s2 h2 r s3 s4 H.
  revert s3 s4.
  induction H; intros. *)
  induction f; intros.
  -
    (* pose proof (sat_req_inv _ _ _ _ _ _ H). *)
    inv H.
    (* apply  *)
  apply sat_req with (h3:=h4); ok.
    subst.
    ok.


  - admit.
  - admit.
  - admit.
Abort. *)

(* Lemma sat_substore : forall f s1 h1 s2 h2 r s3 s4,
  satisfies s1 h1 s2 h2 r f ->
  substore s1 s2 ->
  substore s3 s4 ->
  substore s1 s3 ->
  substore s2 s4 ->
  satisfies s3 h1 s4 h2 r f.
Proof.
  (* intros f s1 h1 s2 h2 r s3 s4 H.
  revert s3 s4.
  induction H; intros. *)
  induction f; intros.
  -
    (* pose proof (sat_req_inv _ _ _ _ _ _ H). *)
    inv H.
  apply sat_req with (h3:=h3); ok.
    subst.
    ok.


  - admit.
  - admit.
  - admit.
Abort. *)

(* Admitted. *)
(* Qed. *)

(* Lemma compose_satisfies : forall f1 f2 s1 h1 s2 h2 s3 h3 s4 r r1 x v,
  satisfies s1 h1 s2 h2 r f1 ->
  satisfies s3 h2 s4 h3 r1 f2 ->
  substore s1 s2 -> (* wf *)
  substore s3 s4 -> (* wf *)

  s3 = supdate x v s2 ->
  (* needed *)
  (* substore s2 s3 -> *)

  s1 x = None -> (* contra *)
  s2 x = None -> (* needed *)
  s3 x = Some v -> (* needed *)
  s4 x = Some v -> (* extension *)
  satisfies s1 h1 s4 h3 r1 (compose x f1 f2).
Proof.
  induction f1; intros.
  - unfold compose.
    simpl.
    (* inv H. *)
    apply sat_ex.
    ok.
    (* the value of the existential *)
    destruct r as [z]; exists z.
    (* after taking p, the intermediate heap is h2 *)
    apply sat_seq with (h3:=h2) (r1:=norm z) (s3:=s3).
    +

    (* sat in smaller store -> sat in larger store *)
    assert (forall s1 h1 s2 h2 r f s3 s4, satisfies s1 h1 s2 h2 r f ->
    substore s1 s3 ->
    substore s2 s4 ->
satisfies s3 h1 s4 h2 r f) as sat_substore.
admit.


apply sat_substore with (s1:=s1) (s2:=s2).
ok.
apply substore_extension; ok.
ok.

+
  (* need inverse? *)
  ok.

(* 
    assert (forall s1 h1 s2 h2 r f s3, satisfies s1 h1 s2 h2 r f -> substore s1 s3 ->
satisfies s3 h1 s2 h2 r f) as sat_substore.
admit.
apply sat_substore with (s1:=s3).
ok.
apply substore_refl.
    admit. *)
    (* exact H0. *)

  - admit.
  - admit.
  - admit.
(* Abort. *)
Admitted.
Qed. *)

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

(** Replacing the return value is monotonic *)
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
    Print sat_ens.
    apply sat_ens with (r:=norm H4) (h2:=hunion h1 h2).
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
  eapply sat_seq with (s3:=s4) (h3:=h4).
  exact H8.

  auto.
  auto.
  admit.
  - admit. *)
  (* Abort. *)
(* Qed. *)

  (* Lemma forward_replace_ret : forall e f x,
    forward e f ->
    forward e (replace_ret x f).
  Proof.
    intros.
    inv H.
    -
    simpl.
      apply fw_const.
      f_equal.
      apply functional_extensionality. intros r.
      apply functional_extensionality. intros s.
      apply functional_extensionality. intros h.
      apply propositional_extensionality.
      split; intros.
      +
        destr H.

      admit.
      + admit.
    - admit.
    - admit.
  Admitted. *)

  (* Lemma aa: forall (s1 s2:store) x v,
    supdate x v s1 = supdate x v s2 -> s1 = s2.
  Proof.
    intros.
    unfold supdate in H.
  Qed. *)

  (* Lemma aa:
    forall f s1 h1 s2 h2 v v1 x,
      (s1 x = None /\ satisfies (supdate x v s1) h1 (supdate x v s2) h2 (norm v) f) <->
      satisfies s1 h1 s2 h2 (norm v1) (replace_ret x f).
  Proof.
    induction f; split; intros; destr H.
    -
      inv H1.
      simpl.
      apply sat_req with (h3:=h4); auto.
      assert (forall (s1 s2:store) x v, supdate x v s1 = supdate x v s2 -> s1 = s2) as H.
      admit.
      (* unfold supdate in Hsu. *)
      (* Check functional_extensionality. *)
      specialize (H _ _ _ _ Hsu).
      auto.
    - admit.
  Admitted. *)

  (* Lemma aa1 :
    forall f s1 h1 s2 h2 x v ,
      satisfies s1 h1 s2 h2 (norm v) (replace_ret x f).
  Proof.
    intros.
    induction f; simpl.
    - eapply sat_req.
      admit.
      admit.
      admit.
      admit.
    - admit.
    - admit.
    - admit.
  Abort.

  Lemma aa :
    forall f s1 h1 s2 h2 x v v1,
      satisfies (supdate x v s1) h1 s2 h2 (norm v1) (replace_ret x f) ->
      exists v2, satisfies (supdate x v s1) h1 s2 h2 (norm v2) f.
  Proof.
    induction f.
    -
    intros.
      simpl in H.
      exists v1.
      assumption.
    -
    intros.
      simpl in H.
      inv H.
      destr Hq.
      exists H.
      apply sat_ens with (h3 := h4).
      auto.
      auto.
      auto.
      subst.
      auto.
    -
      intros.
      simpl in H.
      inv H.

      (* need wf to know s4 has x? *)
      assert (s4 = supdate x v s4). admit.
      rewrite H in Hs2.
      specialize (IHf2 s4 h4 s2 h2 x v v1 Hs2).
      destr IHf2.

      exists H0.
      apply sat_seq with (s3:=s4) (h3:=h4) (r1:=r1).
      auto.
      rewrite H.
      auto.
    -
      intros.
      simpl in H.
      inv H.
      destr Hex.
      (* this is a problem too *)
      assert (replace_ret x f = replace_ret i f). admit.
      rewrite H1 in H0.
      specialize (IHf (supdate x v s1) h1 s2 h2 i H v1 H0).
      destr IHf.
      exists H2.
      (* TODO not done *)

    admit.
  Abort. *)

    (* induction f; intros.
    -
      simpl in H.
      subst.
      assumption.
    -
    assert (forall x p, replace_ret x (ens p) = ens p).
      intros.
      simpl. f_equal.
      apply functional_extensionality. intro r.
      apply functional_extensionality. intro s.
      apply functional_extensionality. intro h.
      apply propositional_extensionality.
      split.
        intros.
        destr H0.
        assert (H1=r).
        admit.
        rewrite <- H2.
        auto.
      (* other direction *)
        intros.
        exists 
      admit.

    rewrite H0 in H.
    auto.
    - admit.
    - admit.
  (* Qed. *)
  Admitted. *)

(* induction on rule. same problem *)

  (* Theorem soundness :
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
            Hb Hs Hf.
    revert se1 he1 se2 he2 re ss1 hs1 ss2 hs2 rs Hb Hs.
    induction Hf.
    - admit.
    - admit.
    -
    intros.
    inv H0.
    destr Hex.
    inv H0.
    inv Hb.
    specialize (IHHf1 _ _ _ _ _ se1 he1 s1 h1 (norm v) H8).

    admit. *)



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
    (* pose proof (compose_satisfies). *)
    destruct Hex as [v1 Hseq].
    (* v1 is the return value of f1, which can be anything due to replace ret *)
    inv Hseq.

    assert (
    forall x v1 ss1 hs1 s4 h4 r1 f1,
satisfies (supdate x v1 ss1) hs1 s4 h4 r1 (replace_ret x f1) ->
satisfies ss1 hs1 s4 h4 (norm v1) f1
    ). admit.
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
    

    (* unfold replace_ret in Hs1. *)
    (* unfold fexists in Hs.  *)
    (* unfold seq in Hseq. destruct Hseq as [s3 [h3 [? [Hrr ?]]]]. *)
    (* unfold replace_ret in Hrr; destruct Hrr as [H10 [H9 H13]]. *)

    (* OLD NOW FIXED now the problem is the IH requires the eval of e1 to take place in the initial stack. but due to the existential adding something to the stack, the evaluation takes place in an extended stack, so we can't apply the IH for e1 *)

    (* OLD NOW FIXED the problem is the positioning of the existential has changed. in the program, it's in the e2 initial stack. in the spec, it's right at the front, in the e1 initial stack, for f1 to assign its ret value to. so somehow need to generalise it, using compiler simulation techniques? there should be an initial relation too, so the spec is allowed to execute in an extended stack. so there's a sim rel between configurations *)

    (* try to meet in the middle *)
    (* apply IHHb2. *)
    (* with (f:=f2) (ss2:=s2) (ss1:=s2) (hs1:=hs2). *)
    (* easy. *)
    (* specialize (IHHb1 f1 (supdate x v s) hs1 s1 h1 (norm v) ). *)
    (* pose proof (substore_extension_trans _ s ss1 v1 x Hsub Hnotin) as Hha. *)

    (* TODO the problem is the ih concerns the same fs, but let does not uniformly transform substructures, there is the replace ret in between.
      and replace ret is defined inductively on the structure of f so i can't simplify it, and don't have any properties to reason about it *)


(* s[x:=v],h ~> s1,h1,norm v |= ens[res] res=1
<->
exists v1. s,h ~> s1,h1,norm v1 |= ens[res] x=1 *)
(* specialize (IHHb1 (replace_ret x f1) (supdate x v1 ss1) hs1 s4 h4 r1). *)

    (* assert (forall s1 h1 s2 h2 f x r v1,
      satisfies (supdate x v1 s1) h1 s2 h2 r (replace_ret x f) ->
      satisfies s1 h1 s2 h2 (norm v1) f
      ) as Hrrs. admit. *)
      (* need a lemma of this form. but this doesn't capture what it does properly *)

    (* assert (forall e f x,
      forward e f ->
      forward e (replace_ret x f)
      ) as Hrrf. admit. *)

    (* assert (forall s1 h1 s2 h2 v f,
      satisfies s1 h1 s2 h2 (norm v) (replace_ret x f) ->
      exists v1, satisfies (supdate x v s1) h1 s2 h2 (norm v1) f
      ) as Hrrs. admit.
      destruct r1.
 *)
    (* specialize (Hrrs _ _ _ _ _ _ _ _ Hs1). *)
    (* destruct Hrrs as [z1 Hrrs]. *)
    (* rewrite supdate_same in Hrrs. *)

    (* specialize (IHHb1 f1 (supdate x v1 ss1) hs1 s4 h4 (norm v) Hha H2 Hrrs). *)

    (* cannot apply because semantics is mismatched *)
    (* specialize (IHHb1 f1 (supdate x v1 ss1) hs1 s4 h4 (norm z) Hha H2 Hs1). *)
    (* cannot apply because forward rules is mismatched *)
    (* specialize (Hrrf _ _ x H2). *)
    (* specialize (IHHb1 (replace_ret x f1) (supdate x v1 ss1) hs1 s4 h4 r1 Hha Hrrf Hs1). *)
(*

    destruct IHHb1 as [IH1 IH2].
    (* we know that evaluation of e1 preserves substore *)

    (* now try to use IH2 *)
    specialize (IHHb2 f2 s3 h3 ss2 hs2 rs).
    apply IHHb2; auto.
    apply (substore_extension_left _ s1 s3 v x IH1).
    unfold compatible in IH2.
    rewrite <- IH2.
    rewrite H9.
    rewrite supdate_same in H9.
    rewrite supdate_same.
    (* need to know substore (supdate x v1 ss1) H6 is preserved by all spec/f eval *)
    (* but how to know that, as we can give any f *)
    pose proof (forward_wellformed _ _ (supdate x v1 ss1) hs1 s3 h3 (norm H10) H2) as Hf1wf.
    unfold wellformed in Hf1wf.

    apply Hf1wf.
    ok.
    rewrite supdate_same.
    reflexivity.
*)

  Admitted.