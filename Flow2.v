
From Coq Require Import ZArith Lia Bool List String Program.Equality.
From CDF Require Import Common Sequences Separation Tactics HeapTactics.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Definition var := string. *)
(* Definition var_eq := string_dec. *)

(* Definition val := Z. *)
Inductive val :=
  | vint : Z -> val
  | vfun : ident -> expr -> val
  | vfix : ident -> ident -> expr -> val

(* Inductive *)
with
expr : Type :=
  | pvar (x: ident)
  | pval (v: val)
  (* | pconst (n: val) *)
  | plet (x: ident) (e1: expr) (e2: expr)
  | pfix (f: ident) (x: ident) (e: expr)
  | pfun (x: ident) (e: expr)
  (* | pref (x: ident) *)
  (* | pderef (x: ident) *)
  (* | passign (x1: ident) (x2: ident) *)
  | pif (x: val) (e1: expr) (e2: expr)
  | pcall (x: val) (a: val)
  .

Fixpoint subst (y:ident) (w:val) (e:expr) : expr :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if ident_eq x y then t1 else t2 in
  match e with
  | pval v => pval v
  | pvar x => if_y_eq x (pval w) e
  | pfun x t1 => pfun x (if_y_eq x t1 (aux t1))
  | pfix f x t1 => pfix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | pcall t1 t2 => pcall t1 t2
  (* | trm_seq t1 t2 => trm_seq (aux t1) (aux t2) *)
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  | pif t0 t1 t2 => pif t0 (aux t1) (aux t2)
  end.

Inductive eresult : Type :=
  | enorm : val -> eresult
.

(* Reserved Notation " 'eval[' s ',' h ',' e ']' '=>' '[' s1 ',' h1 ',' r ']' " (at level 50, left associativity). *)

(* Definition store := store Z. *)

(* Inductive bigstep : store -> heap -> expr -> store -> heap -> eresult -> Prop := *)
Inductive bigstep : heap -> expr -> heap -> eresult -> Prop :=
  | eval_pval : forall h v,
    bigstep h (pval v) h (enorm v)

  | eval_pfun : forall h x e,
    bigstep h (pfun x e) h (enorm (vfun x e))

  | eval_pfix : forall h x e f,
    bigstep h (pfix f x e) h (enorm (vfix f x e))

  | eval_app_fun : forall v1 v2 h x e r,
    v1 = vfun x e ->
    bigstep h (subst x v2 e) h r ->
    bigstep h (pcall v1 v2) h r

  | eval_app_fix : forall v1 v2 h x e r f,
    v1 = vfun x e ->
    bigstep h (subst x v2 (subst f v1 e)) h r ->
    bigstep h (pcall v1 v2) h r

    (* no var rule *)
  (* | eval_pvar : forall s h x v,
    (* Some v = s x -> *)
    bigstep s *)
    (* eval[ s, h, pvar x ]=>[ s, h, enorm v] *)
  (* | eval_pconst : forall s h x,
    eval[ s, h, pconst x ] => [ s, h, enorm x] *)
  (* | eval_plet : forall x e1 e2 v s h h2 s2 s1 h1 r,
    eval[ s, h, e1 ] => [ s1, h1, enorm v] ->
    eval[ supdate x v s1, h1, e2 ] => [ s2, h2, r] ->
    eval[ s, h, plet x e1 e2 ] => [ s2, h2, r ] *)
  (* | eval_pref : forall x s (h:heap) l,
    h l = None ->
    eval[ s, h, pref x ] => [ s, hupdate l (s x) h, enorm l]
  | eval_deref : forall x s (h:heap) v,
    h (s x) = Some v ->
    eval[ s, h, pderef x ] => [ s, h, enorm v]
  | eval_assign : forall x1 x2 s h,
    eval[ s, h, passign x1 x2 ] => [ s, hupdate (s x1) (s x2) h, enorm 0] *)

  (* where " 'eval[' s ',' h ',' e ']' '=>' '[' s1 ',' h1 ',' r ']' " := (bigstep s h e s1 h1 r) *)
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
Definition postcond := val -> assertion.

Inductive result : Type :=
  | norm : val -> result.

  Definition compatible r1 r2 :=
    match (r1, r2) with
    | (norm r3, enorm r4) => r3 = r4
  end.

Definition flow := heap -> heap -> result -> Prop.

Definition req : precond -> flow := fun p h1 h2 _ =>
  (* s1 = s2 /\ *)
  (* h3 is the piece taken out satisfying p *)
  exists h3, h1 = hunion h2 h3 /\ hdisjoint h2 h3 /\ p h3.
  (* TODO only true case for now *)

Definition ens : postcond -> flow := fun q => fun h1 h2 r =>
  (* forall v, r = norm v -> *)
  exists v h3,
  (* h3 is the piece satisfying q that is addded to h1 *)
    r = norm v /\ q v h3 /\ h2 = hunion h1 h3 /\ hdisjoint h1 h3.

Definition seq : flow -> flow -> flow := fun f1 f2 h1 h2 r =>
  exists h3 r1,
  f1 h1 h3 r1 /\
  f2 h3 h2 r.

Infix ";;" := seq (at level 80, right associativity).

Definition fex {A:Type} (f:A -> flow) : flow :=
  fun h1 h2 r =>
  exists v,
    (f v) h1 h2 r.

(* Definition replace_ret (v:val) (f:flow) : flow := fun h1 h2 r =>
  (* exists v, Some v = s1 x /\ *)
  (* f s1 h1 s2 h2 (norm v). *)
  (* f h1 h2 (norm v) *)
  r = (norm v) 
  . *)

Definition flow_res (f:flow) (v:val) : Prop :=
  exists h1 h2, f h1 h2 (norm v).

(* Definition replace_ret (v:val) (f:flow) : flow :=
  f ;; ens (fun r => pure (r = v)). *)

Definition empty := ens (fun r => pure True).

(* For reasoning forward from flows in the context *)
Ltac felim :=
  match goal with
  | H : seq _ _ _ _ _ _ _ |- _ => unfold seq in H; destr H
  | H : req _ _ _ _ _ _ |- _ => unfold req in H; destr H; subst
  | H : ens _ _ _ _ _ _ |- _ => unfold ens in H; destr H; subst
  | H : pureconj _ _ _ _ |- _ => unfold pureconj in H; destr H; subst
  end.

Ltac fintro :=
  match goal with
  | |- ens _ _ _ (norm ?v) => unfold ens; do 2 eexists; intuition
  | |- pure _ _ => unfold pure; intuition
  end.

Ltac fexists v :=
  match goal with
  | |- fex _ _ _ _ => unfold fex; exists v
  end.

(* Ltac fsteps :=
  match goal with
  | H : seq _ _ _ _ _ _ _ |- _ => felim; fsteps
  | H : req _ _ _ _ _ _ |- _ => felim; fsteps
  | H : ens _ _ _ _ _ _ |- _ => felim; fsteps
  | H : pureconj _ _ _ _ |- _ => felim; fsteps
  | _ => idtac
  end. *)

(* Definition satisfies s1 h1 s2 h2 r (f:flow) := f s1 h1 s2 h2 r. *)

(* Lemma empty_noop : forall s h r,
  empty s h s h (norm r).
Proof.
  intros.
  unfold empty.
  unfold ens.
  intuition.
  exists r.
  intuition.
  exists hempty.
  intuition heap.
  unfold pure.
  intuition.
Qed. *)


(* solve a heap goal.
  termination is guaranteed by ordering of lemmas to use *)
Ltac hstep :=
  match goal with
  (* | [ H: _ = hunion hempty _ |- _ ] =>
      rewrite hunion_empty in H
  | [ H: _ = hunion _ hempty |- _ ] =>
      rewrite hunion_comm in H;
      rewrite hunion_empty in H *)
  | [ |- ?h = hunion hempty ?h ] =>
      rewrite hunion_empty; reflexivity
  | [ |- ?h = hunion ?h hempty ] =>
      rewrite hunion_comm; hstep
  | [ |- hdisjoint hempty _ ] =>
      apply hdisjoint_empty
  | [ |- hdisjoint _ hempty ] =>
      rewrite hdisjoint_sym; hstep
  (* | [ |- hunion hempty _ = _ ] =>
      rewrite hunion_empty
  | [ |- _ = hunion _ hempty ] =>
      rewrite hunion_comm; rewrite hunion_empty
  | [ |- hunion _ hempty = _ ] =>
      rewrite hunion_comm;
      rewrite hunion_empty *)
  (* | [ |- ?g ] => idtac *)
  end.


Module SemanticsExamples.

  Definition f1 : flow := ens (fun r => pure (r=vint 1)).
  Definition f2 : flow := fex (fun x => req (fun h => x = vint 1)).
  Definition f3 : flow := f1 ;; f2.

  Example ex1: forall h, f1 h h (norm (vint 1)).
    intros.
    unfold f1.
    fintro.
    (* unfold ens. *)
    (* exists (vint 1). *)
    (* intuition. *)
    (* exists hempty. *)
    (* intuition. *)
    fintro.
    (* unfold pure. *)
    (* intuition. *)
    hstep.
    hstep.
  Qed.

  Example ex2_ret: flow_res f1 (vint 1).
    unfold flow_res. exists hempty. exists hempty.
    unfold f1.
    fintro.
    (* unfold ens.
    exists (vint 1).
    intuition.
    exists hempty.
    intuition. *)
    fintro.
    (* unfold pure. *)
    (* intuition. *)
    hstep.
    hstep.
  Qed.

  Example ex3_req_ret: flow_res f2 (vint 2).
    unfold flow_res.
    exists hempty.
    exists hempty.
    unfold f2.
    fexists (vint 1).
    unfold req.
    exists hempty.
    intuition.
    hstep.
    hstep.
  Qed.

  (* Example ex2: forall h, (replace_ret (vint 2) f1) h h (norm (vint 2)).
    intros.
    unfold f1.
    unfold replace_ret.
    unfold seq.
    exists h.
    exists (norm (vint 1)).
    split.
    - unfold ens.
      exists (vint 1).
      intuition.
      exists hempty.
      intuition.
    hstep.
    hstep.
    unfold pure.
    intuition.
    - unfold ens.
      exists (vint 2).
      intuition.
      exists hempty.
      intuition.
    hstep.
    hstep.
    intuition.
    unfold pure.
    intuition.
Qed. *)

  (* ex z; req x->z; ens[r] x->1/\r=1 *)
  (* Definition f3 : flow :=
    fex "z" (req (pts "x" "z") ;; ens (fun r => (r=1) //\\ ptsval "x" 1)).

  Example ex_sem_f1:
    f1 sempty hempty sempty hempty (norm 1).
    (* sem[true, sempty, hempty]=>[true, sempty, hempty, norm(1)] |= f1. *)
  Proof.
    unfold f1.
    unfold ens.
    intuition auto.
    exists 1.
    intuition.
    exists hempty.
    heap.
    unfold pure.
    intuition auto.
  Qed.

  Example ex_sem_f3:
    f3 (supdate "x" 2 sempty) (hupdate 2 3 hempty) 
      (supdate "z" 3 (supdate "x" 2 sempty)) (hupdate 2 1 hempty) (norm 1).
  Proof.
    unfold f3.
    unfold fex.
    intuition auto.
    exists 3. (* the initial value of z in ex z. x->z, which is given *)
    unfold seq.
    intuition auto.
    exists (supdate "z" 3 (supdate "x" 2 sempty)).
    exists hempty.
    exists (norm 5). (* ret of req, can be anything *)
    split.
    - unfold req.
      intuition auto.
      exists (hupdate 2 3 hempty).
      heap.
      unfold pts.
      unfold contains.
      rewrite supdate_other; try congruence.
      rewrite supdate_same.
      rewrite supdate_same.
      eauto.
    - unfold ens.
      intuition auto.
      exists 1.
      intuition auto.
      exists (hupdate 2 1 hempty).
      heap.
      unfold pureconj.
      intuition auto.
      unfold ptsval.
      unfold contains.
      rewrite supdate_other; try congruence.
      rewrite supdate_same.
      eauto.
  Qed. *)

End SemanticsExamples.


(** * Hoare rules *)

(* forward rules say how to produce a staged formula from a program *)
Inductive forward : expr -> flow -> Prop :=
  | fw_val: forall n,
    forward (pval n) (ens (fun res => pure (res = n)))

  (* there is no need for fw_var/a store because substitution will take care of it before it is reached *)

  | fw_let: forall x e1 e2 f1 f2 v,
    forward e1 f1 ->
    flow_res f1 v ->
    forward (subst x v e2) f2 ->
    forward (plet x e1 e2) (f1 ;; f2)

  (* | fw_deref: forall x y,
    forward (pderef x) (fex y (req (pts x y);;
      ens (fun res s h => ((res = s y) //\\ pts x y) s h)))

  | fw_ref: forall x y,
    (* forward (pref x) (fex (fun y => ens (fun r s h => contains y (s x) s h))) *)
    forward (pref x) (fex y (ens (fun r s h => (r = s y) /\ (pts y x s h)))) *)

  (* | fw_get: forall l v, 
    forward (GET l)
      (req (contains l v) ;;
      (ens (fun r => (r = v) //\\ contains l v))) *)
.

Section ForwardExamples.

  (* let x = 1 in x *)
  Definition e1 := (plet "x" (pval (vint 1)) (pvar "x")).
  Definition f1 :=
    ens (fun v => pure (v = vint 1)) ;;
    ens (fun r => pure (r = vint 1)).

  Example ex1:
    forward e1 f1.
  Proof.
    eapply fw_let.
    - apply fw_val.
    - unfold flow_res.
      exists hempty.
      exists hempty.
      fintro.
      fintro.
      hstep.
      hstep.
    - simpl.
      apply fw_val.
  Qed.

End ForwardExamples.

(*

Definition wellformed (f:flow) s1 h1 s2 h2 r :=
  (* satisfies s1 h1 s2 h2 r f -> substore s1 s2. *)
  f s1 h1 s2 h2 r -> substore s1 s2.

Lemma replace_ret_wellformed : forall x f s1 h1 s2 h2 v,
  Some v = s1 x ->
  wellformed f s1 h1 s2 h2 (norm v) ->
  (wellformed (replace_ret x f)) s1 h1 s2 h2 (norm v).
Proof.
  intros.
  unfold wellformed.
  intros.
  (* unfold satisfies in H1. *)
  unfold replace_ret in H1; destr H1.
  apply H0.
  (* unfolds. *)
  congruence.
Qed.

(* we could prove _wellformed lemmas for all req, ens, etc., but currently we're doing it only for the structures generated from the forward rules *)

Lemma forward_wellformed : forall e f s1 h1 s2 h2 r,
forward e f -> (wellformed f) s1 h1 s2 h2 r.
Proof.
intros e f s1 h1 s2 h2 r H.
revert s1 h1 s2 h2 r.
induction H; intros.
- unfold wellformed; intros.
  unfold ens in H; destr H; subst.
  apply substore_refl.
- unfold wellformed; intros.
  unfold ens in H; destr H; subst.
  apply substore_refl.
-
  unfold wellformed; intros.
  unfold fex in H2. destruct H2 as [? [v H5]]. subst.
  unfold seq in H5. destruct H5 as [s3 [h3 [? [Hrr Hf2]]]]. subst.

  (* introduce well-formed lemma on replace_ret *)
  pose proof (replace_ret_wellformed x f1 (supdate x v s1) h1 s3 h3 v) as Hret.
  rewrite supdate_same in Hret.
  assert (Some v = Some v) as triv. reflexivity.
  specialize (Hret triv); clear triv.

  (* assuming f1 is wf using the IH, replace_ret f1 is wf *)
  specialize (IHforward1 (supdate x v s1) h1 s3 h3 (norm v)).
  specialize (Hret IHforward1).
  unfold wellformed in Hret.
  specialize (Hret Hrr).

  unfold wellformed in IHforward2.
  specialize (IHforward2 s3 h3 s2 h2 r Hf2).

  unfold wellformed in IHforward1.
  unfold replace_ret in Hrr; destruct Hrr as [? [? Hf1]]; rewrite supdate_same in H1; inj H1.
  specialize (IHforward1 Hf1).
  assert (substore s1 (supdate x v s1)).
  apply substore_extension; ok.
  apply substore_trans with (s2 := supdate x v s1); ok.
  apply substore_trans with (s2 := s3); ok.
Qed.

(* {ens emp} e {\phi}, 
SH = { (check, s1, h1, R1)   |  [check, S, h] ~~>m [check, s1, h2, R1] |= \phi }, and 
[S, h, e] -----> [S2, h2, R2], R2!=\bot, 
such that: 
\exists (check, s3, h3, R3) \in SH, s3 \subset s2, h3 \subset h2, R2=R1 *)
  Theorem soundness :
  forall se1 he1 e se2 he2 re (**) f ss1 hs1 ss2 hs2 rs,
    bigstep se1 he1 e se2 he2 re ->
    substore se1 ss1 ->
    (* he1 = hs1 -> *)
    forward e f ->
    f ss1 hs1 ss2 hs2 rs ->
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
      unfold ens in Hs; destr Hs. subst.
      unfold emp in H9.
      unfold compatible.
      heap.
      unfold substore in Hsub.
      symmetry in H.
      specialize (Hsub v x H).
      congruence.
    -
      inv Hf.
      unfold ens in Hs; destr Hs; subst.
      unfold compatible.
      unfold pureconj in H6.
      intuition auto.

    -
    (* we have an IH for each subexpr *)
    (* v is the intermediate result of evaluating e1 *)
    (* r is the final result *)
    (* invp Hf [H2 H4]. *)
    inv Hf.
    (* invp Hf [ | |Hff1 Hff2]. *)
    (* inversion Hf as [ Hy Hz |  |Hff1 Hff2 Hz]. subst; clear Hf. *)
    (* the spec is of the form ex x. f1[x/r];f2 *)
    unfold fex in Hs. destruct Hs as [Hnotin [v1 Hseq]].
    (* see how it evaluates *)
    unfold seq in Hseq. destruct Hseq as [s3 [h3 [? [Hrr ?]]]].
    unfold replace_ret in Hrr; destruct Hrr as [H10 [H9 H13]].


    (* OLD NOW FIXED now the problem is the IH requires the eval of e1 to take place in the initial stack. but due to the existential adding something to the stack, the evaluation takes place in an extended stack, so we can't apply the IH for e1 *)

    (* OLD NOW FIXED the problem is the positioning of the existential has changed. in the program, it's in the e2 initial stack. in the spec, it's right at the front, in the e1 initial stack, for f1 to assign its ret value to. so somehow need to generalise it, using compiler simulation techniques? there should be an initial relation too, so the spec is allowed to execute in an extended stack. so there's a sim rel between configurations *)

    (* try to meet in the middle *)
    (* apply IHHb2. *)
    (* with (f:=f2) (ss2:=s2) (ss1:=s2) (hs1:=hs2). *)
    (* easy. *)
    (* specialize (IHHb1 f1 (supdate x v s) hs1 s1 h1 (norm v) ). *)
    pose proof (substore_extension_trans _ s ss1 v1 x Hsub Hnotin) as Hha.
    specialize (IHHb1 f1 (supdate x v1 ss1) hs1 s3 h3 (norm H10) Hha H2 H13).
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

    (* assert (Hpreserve : substore (supdate x v1 ss1) s3). admit. *)
    (* apply Hf1wf. *)
    (* unfold substore in Hpreserve. *)
    (* apply Hpreserve. *)
    apply Hf1wf.
    ok.
    rewrite supdate_same.
    reflexivity.

(* https://xavierleroy.org/courses/EUTypes-2019/slides.pdf *)

  Qed.

(** * Semantic flows *)
Definition triple (pre:flow) (e:expr) (spec:flow) : Prop :=
  forall s1 h1 s2 h2 r sr s0 h0 r0 s3 h3,
      pre s0 h0 s1 h1 r0 ->
      bigstep s1 h1 e s2 h2 r ->
      spec s0 h0 s3 h3 sr ->
      compatible sr r /\ h2 = h3.

Definition triple_tabula_rasa (e:expr) (spec:flow) : Prop :=
  triple empty e spec.
  
  (*
    {pre} e {spec}
    s,h |= pre
    s,h,e -> s1,h1,v
    -------------------
    s,h,e ~> s1,h1,v |= spec
  *)
(* . *)

Lemma flow_det : forall s h s1 h1 r1 s2 h2 r2 (f:flow),
    f s h s1 h1 r1 ->
    f s h s2 h2 r2 ->
    s1 = s2 /\ h1 = h2 /\ r1 = r2.
Proof.
  intros.
  (* destruct H. *)
  admit.
Admitted.

Lemma fw_const1 : forall p n,
  triple p (pconst n) (p ;; ens (fun res => (res = n) //\\ emp)).
Proof.
  intros.
  unfold triple.
  intros.
  match goal with | H : bigstep _ _ _ _ _ _ |- _ => inv H end.
  split.
  - felim.
    felim.
    felim.
    unfold compatible.
    ok.
  - felim.
  felim.
  felim.
  specialize (flow_det s0 h0 s2 h2 r0 s3 H1 H2 p H H3).
  destr flow_det.
  unfold emp in H4.
  subst.
  heap.
  (* TODO substore then needs simulation relation *)
Abort.
(* Qed. *)

*)
