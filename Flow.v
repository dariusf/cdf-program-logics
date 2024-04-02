
From Coq Require Import ZArith Lia Bool List String Program.Equality.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Common Sequences Separation2.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* some old tactics *)

(* Tactic Notation "inv" constr(h) := inversion h; subst. *)
Tactic Notation "inj" constr(h) := injection h as h; subst.
Tactic Notation "ok" := intuition auto; try easy.

(* these could be made less powerful in future, so they can't be used wrongly *)
Tactic Notation "vacuous" := easy.
(* Tactic Notation "ih" := ok. *)

Tactic Notation "case_on" constr(e) := let H := fresh in destruct e eqn:H; ok.
Tactic Notation "case_on" constr(e) ident(x) := destruct e eqn:x; ok.
(* Tactic Notation "gen" ident_list(x) := generalize dependent x. *)

(* new ones *)

Ltac inv H := inversion H; clear H; subst.

Ltac HUNION n :=
  match n with
  | O => idtac "out of fuel"
  | S ?n' =>
  intuition;
    match goal with
    | [ H: _ = hunion hempty _ |- _ ] =>
    (* let t := type of H in idtac "empty" t n'; *)
        rewrite hunion_empty in H;
        HUNION n'
    | [ H: _ = hunion _ hempty |- _ ] =>
        rewrite hunion_comm in H;
        HDISJ;
        rewrite hunion_empty in H;
        HUNION n'
    | [ |- _ = hunion hempty _ ] =>
        rewrite hunion_empty; HUNION n'
    | [ |- hunion hempty _ = _ ] =>
        rewrite hunion_empty; HUNION n'
    | [ |- _ = hunion _ hempty ] =>
        rewrite hunion_comm; HDISJ; rewrite hunion_empty; HUNION n'
    | [ |- hunion _ hempty = _ ] =>
        rewrite hunion_comm; HDISJ;
        rewrite hunion_empty;
        HUNION n'
    | [ |- ?g ] => auto
    end
  end.

Ltac heap := HUNION (3%nat); HDISJ; auto.

(* Ltac rw := rewrite. *)
(* Ltac con := constructor. *)

(* https://github.com/tchajed/coq-tricks/blob/master/src/Deex.v *)
(* Ltac deex :=
  repeat match goal with
         | [ H: exists (name:_), _ |- _ ] =>
           let name' := fresh name in
           destruct H as [name' H]
         end. *)

Ltac destr H :=
  match type of H with
  | ex _ =>
    let L := fresh in
    let R := fresh in
    destruct H as [L R]; destr R
  (* | [ H: exists (name:_), _ |- _ ] =>
    let name' := fresh name in
    destruct H as [name' H] *)
  | _ /\ _ =>
    let L := fresh in
    let R := fresh in
    destruct H as [L R]; destr L; destr R
  | _ => idtac
  end.

Module Biabduction.

  (* like the member predicate. or modulo equivalence? *)
  Inductive split : assertion -> assertion -> assertion -> Prop :=
    | split_one : forall h2 x y,
      split (pts x y ** h2) (pts x y) h2

    | split_next : forall h2 x y h h1,
      split h1 h h2 ->
      split (pts x y ** h2) h h2
  .

  Inductive biab : assertion -> assertion -> assertion -> Prop :=

    | biab_base : forall s m,
      biab s m (pure True)

    | biab_missing : forall x y a m,
      biab emp ((pts x y) ** m) ((pts x y) ** a)

    | biab_match : forall x y z a b m m1,
      biab b m a ->
      (z = y) //\\ m = m1 ->
      biab ((pts x z) ** b) m1 ((pts x y) ** a)
  .

  Example ex1 : forall x y a b,
    biab (pts x y ** emp) (pts a b) (pts x y ** pts a b).
  Proof.
    intros.
    apply biab_match with (m := pts a b).
    (* apply biab_missing with (m := pts a b). *)

  Admitted.

End Biabduction.

Module Flow3.

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


Module StagesDeep.

  Inductive stages : Type :=
    | req : precond -> stages
    | ens : postcond -> stages
    | seq : stages -> stages -> stages
    (* | fexists : (Z -> stages) -> stages. *)
    | fexists : ident -> stages -> stages.

  Definition flow := Z -> stages.

  Infix ";;" := seq (at level 80, right associativity).

  (* Fixpoint replace_ret x f :=
    match f with
    | ens q => ens (fun r s h => ((r = s x) //\\ q (s x)) s h)
    | req p => f
    | seq a b => seq a (replace_ret x b)
    | fexists i f => fexists i (replace_ret x f)
    end. *)

  Inductive result : Type :=
  | norm : Z -> result
  .

  Reserved Notation " 'sem[' t ',' s ',' h ']=>[' t1 ',' s1 ',' h1 ',' r ']' '|=' f " (at level 50, left associativity).

  (* axiomatization of semantics for staged formulae *)
  Inductive satisfies : bool -> store -> heap -> bool -> store -> heap -> result -> flow -> Prop :=
    | sem_req: forall h3 p s1 s2 h1 r r1 f,
      (exists h2, h3 = hunion h1 h2 /\ hdisjoint h1 h2 /\ p s1 h2) ->
      f r1 = req p ->
      sem[true, s1, h3]=>[true, s2, h1, norm r] |= f
    | sem_ens: forall h1 h3 q v s f,
      (exists h2, h3 = hunion h1 h2 /\ hdisjoint h1 h2 /\ q v s h2) ->
      (* f r1 = ens ((r1 = v) //\\ q) -> *)
      f v = ens q ->
      sem[true, s, h1]=>[true, s, h3, norm v] |= f
    | sem_ex: forall s s1 h1 h2 x e r,
      (* the reason we can't use hoas is that the binding to the existential has to appear in the stack... *)
      (exists v, sem[true, supdate x v s, h1]=>[true, s1, h2, r] |= e) ->
      sem[true, s, h1]=>[true, s1, h2, r] |= fun r1 => fexists x (e r1)
    | sem_seq: forall f1 f2 r1 h1 h2 h3 c s1 s2 s3 r2 st1 st2 ff,
      sem[true, s1, h1]=>[true, s2, h2, norm r1] |= f1 ->
      sem[true, s2, h2]=>[c, s3, h3, r2] |= f2 ->
      st1 = f1 r1 ->
      st2 = f2 r1 ->
      ff r1 = (st1;;st2) ->
      sem[true, s1, h1]=>[c, s3, h3, r2] |= ff

  where " 'sem[' t ',' s ',' h ']=>[' t1 ',' s1 ',' h1 ',' r ']' '|=' f " := (satisfies t s h t1 s1 h1 r f)
  .

  Module SemanticsExamples.

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
    Qed.

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

  End SemanticsExamples.

End StagesDeep.

(* Module StagesShallow. *)

  Inductive result : Type :=
    | norm : Z -> result.

  Definition flow := bool -> store -> heap -> bool -> store -> heap -> result -> Prop.

  Definition req : precond -> flow := fun p c1 s1 h1 c2 s2 h2 r =>
    c1 = true /\ c2 = true /\
    s1 = s2 /\
    (* h3 is the piece taken out satisfying p *)
    exists h3, h1 = hunion h2 h3 /\ hdisjoint h2 h3 /\ p s1 h3.
    (* TODO only true case for now *)

  Definition ens : postcond -> flow := fun q c1 s1 h1 c2 s2 h2 r =>
    c1 = true /\ c2 = true /\
    s1 = s2 /\
    (* forall v, r = norm v -> *)
    exists v, r = norm v /\
    (* h3 is the piece satisfying q that is addded to h1 *)
      exists h3, h2 = hunion h1 h3 /\ hdisjoint h1 h3 /\ q v s1 h3.

  Definition seq : flow -> flow -> flow := fun f1 f2 c1 s1 h1 c2 s2 h2 r =>
    c1 = true /\ c2 = true /\
    exists s3 h3 r1,
    f1 c1 s1 h1 true s3 h3 r1 /\
    f2 true s3 h3 c2 s2 h2 r.

  Infix ";;" := seq (at level 80, right associativity).

  (* we can't use hoas for this as the existential binding has to appear in the stack *)
  Definition fexists : ident -> flow -> flow := fun i f c1 s1 h1 c2 s2 h2 r =>
    c1 = true /\ c2 = true /\
    (* s1 i = None /\ *)
    exists v,
      f c1 (supdate i v s1) h1 c2 s2 h2 r.

  Definition replace_ret (x:ident) (f:flow) : flow := fun c1 s1 h1 c2 s2 h2 r =>
    exists v, Some v = s1 x /\
    f c1 s1 h1 c2 s2 h2 (norm v).

  Module SemanticsExamples.

    Definition f1 : flow := ens (fun r => pure (r=1)).
    Definition f2 : flow := req (fun s h => s "x" = Some 1).

    (* ex z; req x->z; ens[r] x->1/\r=1 *)
    Definition f3 : flow :=
      fexists "z" (req (pts "x" "z") ;; ens (fun r => (r=1) //\\ ptsval "x" 1)).

    Example ex_sem_f1:
      f1 true sempty hempty true sempty hempty (norm 1).
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
      f3 true (supdate "x" 2 sempty) (hupdate 2 3 hempty) 
        true (supdate "z" 3 (supdate "x" 2 sempty)) (hupdate 2 1 hempty) (norm 1).
    Proof.
      unfold f3.
      unfold fexists.
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
    Qed.

  End SemanticsExamples.

(* End StagesShallow. *)

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

  Module ForwardExamples.

    (* let x = 1 in x *)
    Example ex_forward_let1:
      exists st, forward (plet "x" (pconst 1) (pvar "x")) st.
    Proof.
      eexists.
      eapply fw_let.
      eapply fw_const.
      eapply fw_var.
      eauto.
      Unshelve.
      exact 3. (* anything is allowed it seems *)
    Qed.

    (* Check ex_intro. *)
    (* ex_intro : forall (A : Type) (P : A -> Prop) (x : A), P x -> exists y, P y *)
    (* Print ex_forward_let1. *)
      (* (fun st : ...) is P *)
      (* (fexists "x" ...) is the witness x, which is what we are after *)
      (* (fw_let "x" ...) is the existential stmt P x, which is a derivation using the rules above, whose type includes the witness *)

  End ForwardExamples.

Definition compatible r1 r2 :=
  match (r1, r2) with
  | (norm r3, enorm r4) => r3 = r4
  end.

Definition wellformed (f:flow) c1 s1 h1 c2 s2 h2 r :=
  f c1 s1 h1 c2 s2 h2 r -> substore s1 s2.

Lemma replace_ret_wellformed : forall x f c1 s1 h1 c2 s2 h2 v,
  Some v = s1 x ->
  wellformed f c1 s1 h1 c2 s2 h2 (norm v) ->
  (wellformed (replace_ret x f)) c1 s1 h1 c2 s2 h2 (norm v).
Proof.
  unfold wellformed.
  intros.
  unfold replace_ret in H1; destr H1.
  apply H0.
  congruence.
Qed.

(* we could prove _wellformed lemmas for all req, ens, etc., but currently we're doing it only for the structures generated from the forward rules *)

Lemma forward_wellformed : forall e f c1 s1 h1 c2 s2 h2 r,
  forward e f -> (wellformed f) c1 s1 h1 c2 s2 h2 r.
Proof.
  intros e f c1 s1 h1 c2 s2 h2 r H.
  revert c1 s1 h1 c2 s2 h2 r.
  induction H; intros.
  - unfold wellformed; intros.
    unfold ens in H; destr H; subst.
    apply substore_refl.
  -
  unfold wellformed; intros.
    unfold ens in H; destr H; subst.
    apply substore_refl.
  -
    unfold wellformed; intros.
    unfold fexists in H2; destr H2; subst.
    unfold seq in H6; destr H6; subst.

    (* introduce well-formed lemma on replace_ret *)
    pose proof (replace_ret_wellformed x f1 true (supdate x H4 s1) h1 true H2 H5 H4) as Hret.
    (* pose proof (replace_ret_wellformed x f1 true (supdate x H4 s1) h1 true s2 h2 H4) as Hret. *)
    rewrite supdate_same in Hret.
    assert (Some H4 = Some H4). reflexivity.
    specialize (Hret H8).
    clear H8.

    (* assuming f1 is wf using the IH, replace_ret f1 is wf *)
    specialize (IHforward1 true (supdate x H4 s1) h1 true H2 H5 (norm H4)).
    specialize (Hret IHforward1).
    (* clear IHforward1. *)
    unfold wellformed in Hret.
    specialize (Hret H7).

    unfold wellformed in IHforward2.
    specialize (IHforward2 true H2 H5 true s2 h2 r H9).

    unfold wellformed in IHforward1.
    unfold replace_ret in H7; destr H7.
    rewrite supdate_same in H7.
    inj H7.
    specialize (IHforward1 H11).
    assert (substore s1 (supdate x H4 s1)).
    apply substore_extension.


    (* apply IHforward2. *)
    (* unfold replace_ret in H6. *)

    (* unfold ens in H; destr H; subst. *)
    (* apply substore_refl. *)
    admit.
Admitted.

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
      f true ss1 hs1 true ss2 hs2 rs ->
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
        unfold ens in Hs; destr Hs.
        subst.
        unfold emp in H11.
        unfold compatible.
        heap.
        unfold substore in Hsub.
        symmetry in H.
        specialize (Hsub v x H).
        congruence.
      - admit.
      -
      (* we have an IH for each subexpr *)
      (* v is the intermediate result of evaluating e1 *)
      (* r is the final result *)
      inv Hf.
      (* the spec is of the form ex x. f1[x/r];f2 *)
      unfold fexists in Hs; destr Hs.
      (* see how it evaluates *)
      inv H5; destr H6.
      unfold replace_ret in H9; destr H9.


      (* OLD NOW FIXED now the problem is the IH requires the eval of e1 to take place in the initial stack. but due to the existential adding something to the stack, the evaluation takes place in an extended stack, so we can't apply the IH for e1 *)

      (* OLD NOW FIXED the problem is the positioning of the existential has changed. in the program, it's in the e2 initial stack. in the spec, it's right at the front, in the e1 initial stack, for f1 to assign its ret value to. so somehow need to generalise it, using compiler simulation techniques? there should be an initial relation too, so the spec is allowed to execute in an extended stack. so there's a sim rel between configurations *)

      (* try to meet in the middle *)
      (* apply IHHb2. *)
      (* with (f:=f2) (ss2:=s2) (ss1:=s2) (hs1:=hs2). *)
      (* easy. *)
      (* specialize (IHHb1 f1 (supdate x v s) hs1 s1 h1 (norm v) ). *)
      assert (Hnotin: ss1 x = None). admit.
      pose proof (substore_extension_trans s ss1 H0 x Hsub Hnotin) as Hha.
      specialize (IHHb1 f1 (supdate x H0 ss1) hs1 H6 H7 (norm H10) Hha H2 H13).
      destruct IHHb1 as [IH1 IH2].
      (* we know that evaluation of e1 preserves substore *)

      (* now try to use IH2 *)
      specialize (IHHb2 f2 H6 H7 ss2 hs2 rs).
      apply IHHb2; auto.
      apply (substore_extension_left s1 H6 v x IH1).
      unfold compatible in IH2.
      rewrite <- IH2.
      rewrite H9.
      rewrite supdate_same in H9.
      rewrite supdate_same.
      (* need to know substore (supdate x H0 ss1) H6 is preserved by all spec/f eval *)
      (* but how to know that, as we can give any f *)
      assert (Hpreserve : substore (supdate x H0 ss1) H6). admit.
      unfold substore in Hpreserve.
      apply Hpreserve.
      rewrite supdate_same.
      reflexivity.

(* https://xavierleroy.org/courses/EUTypes-2019/slides.pdf *)

    Admitted.

  (* Module SpecExamples.
    Example ex_spec_return_anything: exists x,
      sem[ true, sempty, hempty]=>[ true, sempty, hempty, norm x] |= req emp.
    Proof.
      exists 1.
      apply sem_req with (s1 := sempty).
      auto.
      exists hempty.
      repeat split; heap.
    Qed.

    Example ex_spec_ens_1:
      sem[ true, sempty, hempty]=>[ true, sempty, hempty, norm 1] |=
        ens (fun r => (r = 1) //\\ emp).
    Proof.
      apply sem_ens with (s := sempty).
      exists hempty.
      repeat split; heap.
    Qed.

    Example ex_spec_seq: forall x,
      sem[ true, sempty, hupdate x 1 hempty]=>[ true, sempty, hupdate x 1 hempty, norm 2] |= (req (contains x 1);; ens (fun r => (r = 2) //\\ contains x 1)).
    Proof.
      intros.
      apply sem_seq with (s1 := sempty) (h2 := hempty) (r := norm 3).
      - apply sem_req with (s1 := sempty).
      exists (hupdate x 1 hempty).
      repeat split.
      heap.
      heap.
      - apply sem_ens with (s := sempty).
      exists (hupdate x 1 hempty).
      repeat split; heap.
    Qed.
  End SpecExamples. *)

End Flow3.