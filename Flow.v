
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
Tactic Notation "ok" := auto; try easy.

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

Ltac destr H :=
  match type of H with
  | ex _ =>
    let L := fresh in
    let R := fresh in
    destruct H as [L R]; destr R
  | _ /\ _ =>
    let L := fresh in
    let R := fresh in
    destruct H as [L R]; destr L; destr R
  | _ => idtac
  end.

Module Flow3.

  Definition val := Z.

  Inductive expr : Type :=
    | pvar (x: ident)
    | pconst (n: val)
    | plet (x: ident) (e1: expr) (e2: expr)
    | pref (x: ident)
    | pderef (x: ident)
    | passign (x1: ident) (x2: ident)
    | pif (x: ident) (e1: expr) (e2: expr)
    .

  Inductive eresult : Type :=
    | enorm : val -> eresult
  .

  Reserved Notation " 'eval[' s ',' h ',' e ']' '=>' '[' s1 ',' h1 ',' r ']' " (at level 50, left associativity).

  Inductive bigstep : store -> heap -> expr -> store -> heap -> eresult -> Prop :=
    | eval_pvar : forall s h x,
      eval[ s, h, pvar x ]=>[ s, h, enorm (s x)]
    | eval_pconst : forall s h x,
      eval[ s, h, pconst x ] => [ s, h, enorm x]
    | eval_plet : forall x e1 e2 v s h h2 s2 s1 h1 r,
      eval[ s, h, e1 ] => [ s1, h1, enorm v] ->
      eval[ supdate x v s1, h1, e2 ] => [ s2, h2, r] ->
      eval[ s, h, plet x e1 e2 ] => [ s, h2, r ]
    | eval_pref : forall x s (h:heap) l,
      h l = None ->
      eval[ s, h, pref x ] => [ s, hupdate l (s x) h, enorm l]
    | eval_deref : forall x s (h:heap) v,
      h (s x) = Some v ->
      eval[ s, h, pderef x ] => [ s, h, enorm v]
    | eval_assign : forall x1 x2 s h,
      eval[ s, h, passign x1 x2 ] => [ s, hupdate (s x1) (s x2) h, enorm 0]

    where " 'eval[' s ',' h ',' e ']' '=>' '[' s1 ',' h1 ',' r ']' " := (bigstep s h e s1 h1 r)
  .

  Module ProgramExamples.

    Example ex_ref :
      eval[ sempty, hempty, plet "x" (pconst 1) (pref "x") ]=>[ sempty, hupdate 2 1 hempty, enorm 2 ].
    Proof.
      apply eval_plet with (v:=1) (s1:=sempty) (s2:=supdate "x" 1 sempty) (h1:=hempty).
      apply eval_pconst.
      apply eval_pref.
      constructor.
    Qed.

  End ProgramExamples.

Definition precond := assertion.
Definition postcond := Z -> assertion.

  Inductive flow : Type :=
  (* | req : precond -> flow *)
  (* | ens : postcond -> flow *)
  | req : precond -> flow
  | ens : postcond -> flow
  | seq : flow -> flow -> flow
  (* | fexists : (Z -> flow) -> flow *)
  | fexists : ident -> flow -> flow
  .

  Infix ";;" := seq (at level 80, right associativity).

  Fixpoint replace_ret x f :=
    match f with
    | ens q => ens (fun r s h => ((r = s x) //\\ q (s x)) s h)
    | req p => f
    | seq a b => seq a (replace_ret x b)
    | fexists i f => fexists i (replace_ret x f)
    end.

  Inductive result : Type :=
  | norm : Z -> result
  .

  Reserved Notation " 'sem[' t ',' s ',' h ']=>[' t1 ',' s1 ',' h1 ',' r ']' '|=' f " (at level 50, left associativity).

  (* axiomatization of semantics for staged formulae *)
  Inductive satisfies : bool -> store -> heap -> bool -> store -> heap -> result -> flow -> Prop :=
    | sem_req: forall h3 p s1 s2 h1 r,
      (exists h2, h3 = hunion h1 h2 /\ hdisjoint h1 h2 /\ p s1 h2) ->
      sem[true, s1, h3]=>[true, s2, h1, norm r] |= req p
    | sem_ens: forall h1 h3 q v s,
      (exists h2, h3 = hunion h1 h2 /\ hdisjoint h1 h2 /\ q v s h2) ->
      sem[true, s, h1]=>[true, s, h3, norm v] |= ens q
    | sem_ex: forall s h1 h2 x e r,
      (* the reason we can't use hoas is that the binding to the existential has to appear in the stack... *)
      (exists v, sem[true, supdate x v s, h1]=>[true, s, h2, r] |= e) ->
      sem[true, s, h1]=>[true, s, h2, r] |= fexists x e
    | sem_seq: forall f1 f2 r r1 h1 h2 h3 c s s1 s2,
      sem[true, s, h1]=>[true, s1, h2, r] |= f1 ->
      sem[true, s1, h2]=>[c, s2, h3, r1] |= f2 ->
      sem[true, s, h1]=>[c, s2, h3, r1] |= (f1;;f2)

  where " 'sem[' t ',' s ',' h ']=>[' t1 ',' s1 ',' h1 ',' r ']' '|=' f " := (satisfies t s h t1 s1 h1 r f)
  .

    (* forward rules say how to produce a staged formula from a program *)
    Inductive forward : expr -> flow -> Prop :=
      | fw_const: forall n,
        forward (pconst n) (ens (fun res => (res = n) //\\ emp))
      | fw_var: forall x,
        forward (pvar x) (ens (fun res s h => res = s x /\ emp s h))

      | fw_deref: forall x y,
        forward (pderef x) (fexists y (req (pts x y);;
          ens (fun res s h => ((res = s y) //\\ pts x y) s h)))

      | fw_ref: forall x y,
        (* forward (pref x) (fexists (fun y => ens (fun r s h => contains y (s x) s h))) *)
        forward (pref x) (fexists y (ens (fun r s h => (r = s y) /\ (pts y x s h))))
      | fw_let: forall x e1 e2 f1 f2 f3,
        forward e1 f1 ->
        forward e2 f2 ->
        replace_ret "x" f1 = f3 ->
        forward (plet x e1 e2) (fexists "x" (f3 ;; f2))

      (* | fw_get: forall l v, 
        forward (GET l)
          (req (contains l v) ;;
          (ens (fun r => (r = v) //\\ contains l v))) *)
    .

  Module ForwardExamples.
    Example ex_forward_let:
    forward (plet "x" (pconst 1) (pderef "x"))
      (fexists "x" (ens (fun r s h => pure (r = s "x" /\ s "x" = 1) s h);;
      (fexists "z" (req (pts "x" "z");;
        ens (fun res s h => ((res = s "z") //\\ pts "x" "z") s h)))
      ))
      .
    Proof.
      apply fw_let with (f1 := (ens (fun r => pure (r = 1)))).
      apply fw_const.
      apply fw_deref.
      simpl.
      f_equal.
      apply functional_extensionality; intros v.
      apply functional_extensionality; intros s.
      apply functional_extensionality; intros h.
      unfold pureconj.
      unfold pure.
      apply propositional_extensionality.
      intuition auto.
    Qed.
  End ForwardExamples.

(* {ens emp} e {\phi}, 
SH = { (check, s1, h1, R1)   |  [check, S, h] ~~>m [check, s1, h2, R1] |= \phi }, and 
[S, h, e] -----> [S2, h2, R2], R2!=\bot, 
such that: 
\exists (check, s3, h3, R3) \in SH, s3 \subset s2, h3 \subset h2, R2=R1 *)
    Theorem soundness : forall e f s1 s2 s3 h1 h2 h3 r1 r2,
      bigstep s1 h1 e s3 h3 (enorm r2) ->
      forward e f ->
      satisfies true s1 h1 true s2 h2 (norm r1) f ->
      s2 = s3 /\ h2 = h3 /\ r1 = r2.
      (* forall f h3 r, *)
    Proof.
      intros e f s1 s2 s3 h1 h2 h3 r1 r2 Hb.
      (* inv Hb. *)
      (* generalize dependent f.
      generalize dependent s2.
      generalize dependent h2.
      generalize dependent r1. *)
      (* https://stackoverflow.com/questions/4519692/keeping-information-when-using-induction *)
      remember (enorm r2) as t1 in Hb.
      induction Hb; intros Hf Hs.
      -
      (* var. proof comes down to the fact that both spec and program read s(x) and leave the heap unchanged.
      the use of r in ens[r] in the paper is not modelled due to HOAS representation of postconditions. *)
 injection Heqt1; intros.
 (* applyf_equal Heqt1. *)
      inv Hf.
      inv Hs.
      destr H3.
      unfold emp in H4.
      (* subst. *)
      rewrite H4 in H1.
      (* rewrite hunion_comm in H1. *)
      (* rewrite hunion_empty in H1. *)
      (* HUNION1 (3)%nat. *)
      heap.
      (* heap. *)
      (* heap. *)
      (* auto. *)
      (* rewrite hunion_empty in H1; *)
      (* heap. *)
      (* intuition heap. *)
      (* HDISJ. *)

      (* intuition heap. *)
      (* apply sem_ens. *)
      (* exists hempty. *)
      - admit.
      -
      subst r.
      inv Hf.

      admit.
      - admit.
      - admit.
      - admit.
    Admitted.

    (* Theorem soundness : forall s1 h e1 s2 h1 h2,
      bigstep s1 h e1 s2 h1 h2 ->
      forall f h3 r,
      forward e1 f ->
      satisfies true s1 h1 true s2 h3 (norm r) f.
    Proof.
     intros s h e1 s1 h1 h2 Hb.
     induction Hb; intros.
     - inv H.
     apply sem_ens.
     exists hempty.
      admit.
      admit.
      admit.
     - admit.
     - admit.
     - admit.
     - admit.
     - admit.
    Admitted. *)

  Module SpecExamples.
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
  End SpecExamples.

End Flow3.