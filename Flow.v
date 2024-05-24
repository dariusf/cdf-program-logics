From Coq Require Import ZArith Lia Bool List String Program.Equality.
From CDF Require Import Common Sequences Separation2 Tactics HeapTactics.
(* From Coq Require Import ssreflect ssrfun ssrbool. *)

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Theorem ident_neq_sym : forall (n:ident) m, n <> m -> m <> n.
Proof.
  intros n m H1 H2; symmetry in H2; false_hyp H2 H1.
Qed.

Inductive expr : Type :=
  | pvar (x: ident)
  | pint (n: Z)
  | plamb (x: ident) (n: expr)
  | plet (x: ident) (e1: expr) (e2: expr)
  (* | pref (x: ident) *)
  (* | pderef (x: ident) *)
  (* | passign (x1: ident) (x2: ident) *)
  (* | pif (x: ident) (e1: expr) (e2: expr) *)
  | pcall (x: ident) (a: ident).

Coercion pint : Z >-> expr.

Inductive val : Type :=
  | vloc (i:Z)
  | vint (i:Z)
  (* need to relate free variables used in a lambda formula to those in the captured env *)
  (* | vclos (x:ident) (e:expr) (s:store val) *)
  | vclos (x:ident) (e:expr)
  .

Coercion vint : Z >-> val.

Inductive eresult : Type :=
  | enorm : val -> eresult.

Reserved Notation " 'eval[' s ',' h ',' e ']' '=>' '[' s1 ',' h1 ',' r ']' " (at level 50, left associativity).

Definition store := store val.
Definition heap := heap val.

Inductive bigstep : store -> heap -> expr -> store -> heap -> eresult -> Prop :=

  | eval_pvar : forall s h x v,
    Some v = s x ->
    eval[ s, h, pvar x ]=>[ s, h, enorm v ]

  | eval_plamb : forall s h x e,
    eval[ s, h, plamb x e ]=>[ s, h, enorm (vclos x e) ]
    (* eval[ s, h, plamb x e ]=>[ s, h, enorm (vclos x e s) ] *)

  | eval_pint : forall s h x,
    eval[ s, h, pint x ] => [ s, h, enorm (vint x) ]

  | eval_plet : forall x e1 e2 v s h h2 s2 s1 h1 r,
    eval[ s, h, e1 ] => [ s1, h1, enorm v] ->
    eval[ supdate x v s1, h1, e2 ] => [ s2, h2, r] ->
    eval[ s, h, plet x e1 e2 ] => [ s2, h2, r ]

  | eval_pcall : forall fn x y e1 sf s h s2 h1 r arg,
    (* s fn = Some (vclos y e1 sf) -> *)
    s fn = Some (vclos y e1) ->
    s x = Some arg ->
    eval[ supdate y arg sf, h, e1 ] => [ s2, h1, r ] ->
    eval[ s, h, pcall fn x ] => [ s, h1, r ]

  (* | eval_pref : forall x s (h:heap) l,
    h l = None ->
    eval[ s, h, pref x ] => [ s, hupdate l (s x) h, enorm l]
  | eval_deref : forall x s (h:heap) v,
    h (s x) = Some v ->
    eval[ s, h, pderef x ] => [ s, h, enorm v]
  | eval_assign : forall x1 x2 s h,
    eval[ s, h, passign x1 x2 ] => [ s, hupdate (s x1) (s x2) h, enorm 0] *)

  where " 'eval[' s ',' h ',' e ']' '=>' '[' s1 ',' h1 ',' r ']' " := (bigstep s h e s1 h1 r).

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

Definition assertion := assertion val.
Definition precond := assertion.
Definition postcond := val -> assertion.

Definition pts (x: ident) (y: ident) : assertion :=
  fun s h =>
    exists v w, Some (vint v) = s x /\ Some w = s y /\
      (contains v w) s h.

Definition ptsval (x: ident) (v: val) : assertion :=
  fun s h =>
    exists w, Some (vint w) = s x /\
      (contains w v) s h.

Inductive result : Type :=
  | norm : val -> result.

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

Fixpoint fresh_in_flow (x:ident) (f:flow) :=
  match f with
  | ens q => True
  | req _ => True
  | seq a b => fresh_in_flow x a /\ fresh_in_flow x b
  | fexists i f => x <> i /\ fresh_in_flow x f
  end.

Lemma fresh_replace : forall f x i,
  fresh_in_flow i (replace_ret x f) ->
  fresh_in_flow i f.
Proof.
  induction f; intros; simpl in *; intuition auto.
  - now apply IHf2 with (x:=x).
  - apply IHf with (x:=x).
    easy.
Qed.

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

  | sat_ens q s1 h1 s2 h2 h3 (v:val)
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
    (Hfresh: fresh_in_flow x f)
    (Hex: exists v, satisfies (supdate x v s1) h1 s2 h2 r f) :
    satisfies s1 h1 s2 h2 r (fexists x f).

  (* where " 'sem[' t ',' s ',' h ']=>[' t1 ',' s1 ',' h1 ',' r ']' '|=' f " := (satisfies t s h t1 s1 h1 r f) *)

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
    satisfies s h s h (norm 2) (ens (fun r s h => s x = Some (vint 1))).
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
    fexists "z" (req (pts "x" "z") ;; ens (fun r => (r = 1) //\\ ptsval "x" 1)).

  Example ex_sem_f3:
    satisfies (supdate "x" (vint 2) sempty) (hupdate 2 (vint 3) hempty)
      (supdate "z" (vint 3) (supdate "x" (vint 2) sempty)) (hupdate 2 (vint 1) hempty) (norm (vint 1)) f3.
  Proof.
    unfold f3.
    apply sat_ex.
    heap.
    easy.
    exists (vint 3).
    apply sat_seq with (s3:=supdate "z" (vint 3) (supdate "x" (vint 2) sempty)) (h3:=hempty) (r1:=norm (vint 5)).
    - apply sat_req with (h3:=hupdate 2 (vint 3) hempty).
      reflexivity.
      heap.
      heap.
      unfold pts.
      exists 2.
      exists (vint 3).
      intuition easy.
    - apply sat_ens with (h3:=hupdate 2 (vint 1) hempty); heap.
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
  | fw_int: forall i p,
    p = (ens (fun res => (res = vint i) //\\ emp)) ->
    forward (pint i) p

  | fw_lamb: forall x p e,
    (* cannot check the spec at this point, as lambdas containing flows would be mutually recursive *)
    (* p = (ens (fun res => (res = vclos x e s) //\\ emp)) -> *)
    p = (ens (fun res => (res = vclos x e) //\\ emp)) ->
    forward (plamb x e) p

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
  forward (plet x 1 (pvar x)) (fexists x (
    replace_ret x (ens (fun r => pure (r = 1))) ;;
    ens (fun res s h => exists v, Some v = s x /\ res = v /\ emp s h)
    )).
Proof.
  simpl.
  intros.
  apply fw_let with (f1 := (ens (fun r => pure (r = 1)))).
  - eapply fw_int.
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

Lemma satisfies_replace_ret : forall f x v s1 h1 s2 h2 r,
  fresh_in_flow x f ->
  s1 x = Some v ->
  satisfies s1 h1 s2 h2 r (replace_ret x f) ->
  satisfies s1 h1 s2 h2 (norm v) f.
Proof.
  induction f; intros; simpl in *.
  - inv H1.
    apply sat_req with (h3 := h4); ok.
  - inv H1. destruct Hq as [v1 [H3 H2]].
    rewrite H3 in H0; inj H0.
    apply sat_ens with (h3 := h4); ok.
  - inv H1.
    pose proof (satisfies_monotonic _ _ _ _ _ _ Hs1) as Hmono1.
    pose proof (substore_mem _ s1 s4 v x Hmono1 H0) as Hs.
    destruct H as [Hf1 Hf2].
    specialize (IHf2 x v s4 h4 s2 h2 r Hf2 Hs Hs2).
    apply sat_seq with (s3:=s4) (h3:=h4) (r1:=r1); ok.
  - inv H1; destruct Hex as [v0 Hsat].
    destruct H as [Hneq Hf].
    pose proof (ident_neq_sym _ _ Hneq) as Hneq1.
    pose proof (supdate_other _ s1 i v0 x Hneq1) as He. rewrite <- He in H0.
    specialize (IHf x v (supdate i v0 s1) h1 s2 h2 r Hf H0 Hsat).
    apply sat_ex; auto.
    apply fresh_replace with (x:=x); easy.
    exists v0.
    auto.
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
  - (* lambda case *)
    inv Hf.
    (* destruct H2 as [s0 Hq]. *)
    (* subst. *)
    inv Hs.
    unfold pureconj in Hq.
    unfold compatible.
    intuition auto.
  - (* int *)
    inv Hf.
    inv Hs.
    unfold compatible.
    unfold pureconj in Hq.
    intuition auto.
  - (* let *)
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

    (* reason about replace_ret using the freshness of existentials *)
    pose proof (satisfies_replace_ret f1 x v1 (supdate x v1 ss1) hs1 s4 h4 r1) as Hrr.
    forward Hrr. {
      simpl in Hfresh.
      destruct Hfresh as [Hfresh _].
      apply (fresh_replace _ _ _ Hfresh).
    }
    forward Hrr by apply supdate_same.
    specialize (Hrr Hs1).
    clear Hfresh.

    (* apply IH1 to know that all of e1 is sound *)
    specialize (IHHb1 f1 (supdate x v1 ss1) hs1 s4 h4 (norm v1)).
    forward IHHb1 by apply substore_extension_trans with (s2:=ss1); auto.
    specialize (IHHb1 H3 Hrr).
    destruct IHHb1 as [Hst Hcomp].
    unfold compatible in Hcomp; subst.

    (* apply IH2 to know that the entire thing is sound *)
    specialize (IHHb2 f2 s4 h4 ss2 hs2 rs).
    forward IHHb2. {
      pose proof (satisfies_monotonic _ _ _ _ _ _ Hs1) as Hmono.
      specialize (substore_extension_left _ s1 s4 v x Hst) as Hsub1.
      now forward Hsub1 by apply (substore_extension_inv _ _ _ _ _ Hmono).
    }
    specialize (IHHb2 H4 Hs2).
    easy.
  - (* call *)
  inv Hf.
Qed.
(* Admitted. *)