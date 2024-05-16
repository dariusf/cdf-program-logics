
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

Definition empty := ens (fun r => pure True).

Infix ";;" := seq (at level 80, right associativity).

Fixpoint replace_ret x f :=
  match f with
  | ens q => ens (fun _ s h => exists v, s x = Some v /\ q v s h)
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

  | sat_req p s1 h1 s2 h2 r h3
    (Hsu: s1 = s2)
    (* h3 is the piece taken out satisfying p *)
    (Hex: h1 = hunion h2 h3)
    (Hd: hdisjoint h2 h3)
    (Hp: p s1 h3) :
    satisfies s1 h1 s2 h2 (norm r) (req p)

  | sat_ens q s1 h1 s2 h2 r h3 v
    (Hsu:s1 = s2)
    (* forall v, r = norm v -> *)
    (Hr: r = norm v)
    (* h3 is the piece satisfying q that is addded to h1 *)
    (Hh: h2 = hunion h1 h3)
    (Hd: hdisjoint h1 h3)
    (Hq: q v s1 h3) :
    satisfies s1 h1 s2 h2 (norm v) (ens q)

  | sat_seq f1 f2 s1 h1 s2 h2 r s3 h3 r1
    (Hs1: satisfies s1 h1 s3 h3 r1 f1)
    (Hs2: satisfies s3 h3 s2 h2 r f2) :
    satisfies s1 h1 s2 h2 r (seq f1 f2)

  (* | sat_ex: forall s s1 h1 h2 x e r,
    (* the reason we can't use hoas is that the binding to the existential has to appear in the stack... *)
    (exists v, , supdate x v s, h1]=>[true, s1, h2, r] |= e) ->
    sem[true, s, h1]=>[true, s1, h2, r] |= fun r1 => fexists x (e r1) *)

  (* | sat_ex: forall x f s1 h1 s2 h2 r,
    s1 x = None ->
    (exists v, satisfies (supdate x v s1) h1 s2 h2 r f) ->
    satisfies s1 h1 s2 h2 r (fexists x f) *)

  | sat_ex
  (* (x:ident) (f:flow) (s1 s2:store) (h1 h2:heap) r *)
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
  apply sat_ens with (h3:=hempty) (r:=norm v); heap.
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
    apply sat_ens with (h3:=hempty) (r:=norm 2); auto.
  - intros.
    simpl.
    inv H.
    apply sat_ens with (h3:=hempty) (r:=norm 2); heap.
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
    - apply sat_ens with (h3:=hupdate 2 1 hempty) (r:=norm 1); heap.
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

  | fw_let: forall x e1 e2 f1 f2 f3,
    forward e1 f1 ->
    forward e2 f2 ->
    replace_ret x f1 = f3 ->
    (* f1 ;; ens (fun _ => ) = f3 -> *)
    forward (plet x e1 e2) (fexists x (f3 ;; f2))

  (* | fw_get: forall l v, 
    forward (GET l)
      (req (contains l v) ;;
      (ens (fun r => (r = v) //\\ contains l v))) *)
.

Example e_fw_let1 : forall x,
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
      apply functional_extensionality. intros r.
      apply functional_extensionality. intros s.
      apply functional_extensionality. intros h.
      apply propositional_extensionality.
      split; intros.
      + destr H.
        intuition.
        exists H0.
        intuition auto.
      + destr H.
      exists H0.
        intuition auto.
  - reflexivity.
Qed.


(* Example e_fw_let : forall x,
(* (fexists x ( ;; ens (fun r s h => r = s x))) *)
exists a b,
  forward (plet x (pconst 1) (pvar x)) (fexists x (a ;; b)).
Proof.
  intros.
  eexists.
  eexists.
  eapply fw_let.
  eapply fw_const.
  reflexivity.
  eapply fw_var.
  reflexivity.
  reflexivity.
  Unshelve.
  exact 1.
Qed.
Print e_fw_let. *)

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

  Lemma aa :
    forall f s1 h1 s2 h2 x v v1,
      satisfies (supdate x v s1) h1 s2 h2 (norm v1) (replace_ret x f) ->
      satisfies (supdate x v s1) h1 s2 h2 (norm v1) f.
  Proof.
  Abort.
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
    destruct Hex as [v1 Hseq].
    inv Hseq.
    (* v1 is the intermediate result of the let, which should = v? *)

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
    pose proof (substore_extension_trans _ s ss1 v1 x Hsub Hnotin) as Hha.

    (* TODO the problem is the ih concerns the same fs, but let does not uniformly transform substructures, there is the replace ret in between.
      and replace ret is defined inductively on the structure of f so i can't simplify it, and don't have any properties to reason about it *)


(* s[x:=v],h ~> s1,h1,norm v |= ens[res] res=1
<->
exists v1. s,h ~> s1,h1,norm v1 |= ens[res] x=1 *)

    assert (forall s1 h1 s2 h2 f x r v v1,
      satisfies (supdate x v s1) h1 s2 h2 r (replace_ret x f) ->
      satisfies (supdate x v s1) h1 s2 h2 (norm v1) f
      ) as Hrrs. admit.
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
    specialize (Hrrs _ _ _ _ _ _ _ _ v Hs1).
    (* destruct Hrrs as [z1 Hrrs]. *)
    (* rewrite supdate_same in Hrrs. *)

    specialize (IHHb1 f1 (supdate x v1 ss1) hs1 s4 h4 (norm v) Hha H2 Hrrs).

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