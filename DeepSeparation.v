(** Heaps and heap assertions for separation logics. *)

From Coq Require Import ZArith Lia Bool String List.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Common Heaps.

Local Open Scope Z_scope.

(** * 2. Assertions for separation logic *)

(* Inductive term : Type :=
  | tvar (x:ident)
  | tint (i:Z)
  | tloc (l:Z).

Fixpoint interp {A:Type} (s:store A) (f:sl) : Prop :=
  match f with
  | pure p => p
  | sep a b =>
    exists h1 h2, slsatisfies s h1 a /\ slsatisfies s h2 b /\
      hdisjoint h1 h2 /\ h = hunion h1 h2
  | pts_to x v => forall v1,
    s v = Some v1 ->
    h = hupdate x v1 hempty
  | emp => h = hempty
  end. *)

Set Implicit Arguments.

Inductive term (T:Type) : Type :=
  | tvar (x:ident)
  | tval (a:T).

Definition replace_term {T:Type} (x:ident) (v:ident) (t:term T) :=
  match t with
  | tvar _ y => if string_dec x y then tvar _ v else t
  | tval _  => t
  end.

Inductive pure (T:Type) : Type :=
  | peq (a:term T) (b:term T)
  | ptrue
  | pfalse
  | por (a:pure T) (b:pure T)
  | pimply (a:pure T) (b:pure T)
  | pand (a:pure T) (b:pure T).

Fixpoint replace_pure {T:Type} (x:ident) (v:ident) (p:pure T) :=
  match p with
  | peq a b => peq (replace_term x v a) (replace_term x v b)
  | ptrue _ => p
  | pfalse _ => p
  | por a b => por (replace_pure x v a) (replace_pure x v b)
  | pand a b => pand (replace_pure x v a) (replace_pure x v b)
  | pimply a b => pimply (replace_pure x v a) (replace_pure x v b)
  end.

Fixpoint pure_satisfies {A:Type} (s:store A) (p:pure A) : Prop :=
  match p with
  | peq a b => a = b
  | ptrue _ => True
  | pfalse _ => False
  | por a b => pure_satisfies s a \/ pure_satisfies s b
  | pand a b => pure_satisfies s a /\ pure_satisfies s b
  | pimply a b => pure_satisfies s a -> pure_satisfies s b
  end.

Inductive sl (T:Type) : Type :=
  | pi (p:pure T)
  | sep (a:sl T) (b:sl T)
  | pts_to (a:addr) (b:ident)
  | emp.

Fixpoint replace_sl {T:Type} (x:ident) (v:ident) (s:sl T) :=
  match s with
  | pi p => pi (replace_pure x v p)
  | sep a b => sep (replace_sl x v a) (replace_sl x v b)
  | pts_to _ _ _ => s
  | emp _ => s
  end.

Fixpoint sl_satisfies {A:Type} (s:store A) (h:heap A) (f:sl A) : Prop :=
  match f with
  | pi p => pure_satisfies s p
  | sep a b =>
    exists h1 h2, sl_satisfies s h1 a /\ sl_satisfies s h2 b /\
      hdisjoint h1 h2 /\ h = hunion h1 h2
  | pts_to _ x v => forall v1,
    s v = Some v1 ->
    h = hupdate x v1 hempty
  | emp _ => h = hempty
  end.

(* Inductive slf :=
  | pts . *)

(* Definition assertion (A:Type) : Type := store A -> heap A -> Prop.

(** Implication (entailment). *)

Definition aimp {A:Type} (P Q: assertion A) : Prop :=
  forall s h, P s h -> Q s h.

Notation "P -->> Q" := (aimp P Q) (at level 95, no associativity).

(** Quantification. *)

Definition aexists {A: Type} {T} (P: A -> assertion T) : assertion T :=
  fun s h => exists a: A, P a s h.

Definition aforall {A: Type} {T} (P: A -> assertion T) : assertion T :=
  fun s h => forall a: A, P a s h.

(** The assertion "the heap is empty". *)

Definition emp {A:Type} : assertion A :=
  fun s h => h = hempty.

(** The pure assertion: "the heap is empty and P holds". *)

Definition pure {A:Type} (P: Prop) : assertion A :=
  fun s h => P /\ h = hempty.
  (* TODO pure assertions *)

(** The assertion "address [l] contains value [v]". 
    The domain of the heap must be the singleton [{l}]. *)

Definition contains {A:Type} (l: addr) (v: A) : assertion A :=
  fun s h => h = hupdate l v hempty.

(* Definition pts {A:Type} (x: ident) (y: ident) : assertion A :=
  fun s h =>
    exists v w, Some v = s x /\ Some w = s y /\
      (contains v w) s h. *)

(* Definition ptsval {A:Type} (x: ident) (v: A) : assertion A :=
  fun s h =>
    exists w, Some w = s x /\
      (contains w v) s h. *)

(** The assertion "address [l] is valid" (i.e. in the domain of the heap). *)

Definition valid {A:Type} (l: addr) : assertion A := aexists (contains l).

(** The separating conjunction. *)

Definition sepconj {A:Type} (P Q: assertion A) : assertion A :=
  fun s h => exists h1 h2, P s h1
                      /\ Q s h2
                      /\ hdisjoint h1 h2  /\ h = hunion h1 h2.

Notation "P ** Q" := (sepconj P Q) (at level 60, right associativity).

(** The conjunction of a simple assertion and a general assertion. *)

Definition pureconj {A:Type} (P: Prop) (Q: assertion A) : assertion A :=
  fun s h => P /\ Q s h.
  (* TODO pure assertions *)

Notation "P //\\ Q" := (pureconj P Q) (at level 60, right associativity).

(** Plain conjunction and disjunction. *)

Definition aand {A:Type} (P Q: assertion A) : assertion A :=
  fun s h => P s h /\ Q s h.
Definition aor {A:Type} (P Q: assertion A) : assertion A :=
  fun s h => P s h \/ Q s h.

(** Extensional equality between assertions. *)

Lemma assertion_extensionality:
  forall {A:Type} (P Q: assertion A),
  (forall s h, P s h <-> Q s h) -> P = Q.
Proof.
  intros. apply functional_extensionality. intros s.
  apply functional_extensionality. intros h.
  apply propositional_extensionality. auto.
Qed.

(** ** Properties of separating conjunction *)

Lemma sepconj_comm: forall {A:Type} (P Q:assertion A), P ** Q = Q ** P.
Proof.
  assert (forall {A:Type} (P Q:assertion A) s h, (P ** Q) s h -> (Q ** P) s h).
  { intros A P Q s h (h1 & h2 & P1 & Q2 & EQ & DISJ); subst h.
    exists h2, h1; intuition auto.
    apply hdisjoint_sym; auto.
    symmetry; apply hunion_comm; auto. } 
  intros; apply assertion_extensionality; intros; split; auto.
Qed.

Lemma sepconj_assoc: forall {A:Type} (P Q R:assertion A), (P ** Q) ** R = P ** (Q ** R).
Proof.
  intros; apply assertion_extensionality; intros; split.
- intros (hx & h3 & (h1 & h2 & P1 & Q2 & EQ & DISJ) & R3 & EQ' & DISJ'). subst hx h.
  rewrite hdisjoint_union_l in EQ'. rewrite hunion_assoc.
  exists h1, (hunion h2 h3); intuition auto.
  exists h2, h3; intuition auto.
  rewrite hdisjoint_union_r; tauto.
- intros (h1 & hx & P1 & (h2 & h3 & Q2 & R3 & EQ & DISJ) & EQ' & DISJ'). subst hx h.
  rewrite hdisjoint_union_r in EQ'. rewrite <- hunion_assoc.
  exists (hunion h1 h2), h3; intuition auto.
  exists h1, h2; intuition auto.
  rewrite hdisjoint_union_l; tauto.
Qed.

Lemma sepconj_emp: forall {A:Type} (P:assertion A), emp ** P = P.
Proof.
  intros; apply assertion_extensionality; intros; split.
- intros (h1 & h2 & EMP1 & P2 & EQ & DISJ). red in EMP1. subst h h1.
  rewrite hunion_empty; auto.
- intros. exists hempty, h; intuition auto. 
  red; auto.
  red; auto.
  rewrite hunion_empty; auto.
Qed.

Lemma sepconj_imp_l: forall {A:Type} (P Q R:assertion A),
  (P -->> Q) -> (P ** R -->> Q ** R).
Proof.
  intros A P Q R IMP s h (h1 & h2 & P1 & Q2 & D & U).
  exists h1, h2; intuition auto.
Qed.

Lemma sepconj_imp_r: forall {A:Type} (P Q R:assertion A),
  (P -->> Q) -> (R ** P -->> R ** Q).
Proof.
  intros. rewrite ! (sepconj_comm R). apply sepconj_imp_l; auto.
Qed.

(** ** Other useful logical properties *)

Lemma pure_sep: forall {T:Type} (P Q:Prop),
  pure (P /\ Q) = (pure P:assertion T) ** pure Q.
Proof.
  intros. apply assertion_extensionality; intros.
  unfold pure, sepconj. split.
- intros ((A & B) & C). subst h. exists hempty, hempty; intuition auto.
  intro; auto.
  rewrite hunion_empty; auto.
- intros (h1 & h2 & (PP & E1) & (QQ & E2) & C & D).
  subst. rewrite hunion_empty; auto.
Qed.

Lemma pureconj_sepconj: forall {T} (P:Prop) (Q:assertion T),
  pure P ** Q = P //\\ Q.
Proof.
  intros. apply assertion_extensionality; intros.
  unfold pure, sepconj, pureconj; split.
- intros (h1 & h2 & (A & B) & C & D & E).
  split. auto. subst. rewrite hunion_empty. auto.
- intros (A & B). exists hempty, h; intuition auto.  
  intro l. auto.
  rewrite hunion_empty; auto.
Qed.

Lemma lift_pureconj: forall {A:Type} (P:Prop) (Q R:assertion A), (P //\\ Q) ** R = P //\\ (Q ** R).
Proof.
  intros. rewrite <- ! pureconj_sepconj. rewrite sepconj_assoc. auto.
Qed.

Lemma lift_aexists: forall (A: Type) (P: A -> assertion A) (Q:assertion A),
  aexists P ** Q = aexists (fun x => P x ** Q).
Proof.
  intros; apply assertion_extensionality; intros; split.
- intros (h1 & h2 & (a & P1) & Q2 & DISJ & EQ).
  exists a, h1, h2; auto.
- intros (a & h1 & h2 & P1 & Q2 & DISJ & EQ).
  exists h1, h2; intuition auto. exists a; auto.
Qed.

Lemma sepconj_swap3: forall {A:Type} (R P Q:assertion A),
  P ** Q ** R = R ** P ** Q.
Proof.
  intros. rewrite <- sepconj_assoc, sepconj_comm. auto.
Qed. 

Lemma sepconj_swap4: forall {A:Type} (S P Q R:assertion A),
  P ** Q ** R ** S = S ** P ** Q ** R.
Proof.
  intros. rewrite <- sepconj_assoc, sepconj_swap3, sepconj_assoc. auto.
Qed. 

Lemma sepconj_pick2: forall {A:Type} (Q P R:assertion A),
  P ** Q ** R = Q ** P ** R.
Proof.
  intros. rewrite (sepconj_comm Q), <- sepconj_assoc, sepconj_comm. auto.
Qed. 

Lemma sepconj_pick3: forall {A:Type} (R P Q S:assertion A),
  P ** Q ** R ** S = R ** P ** Q ** S.
Proof.
  intros. rewrite (sepconj_pick2 R), (sepconj_pick2 P). auto. 
Qed.

(** ** Magic wand *)

Definition wand {A:Type} (P Q: assertion A) : assertion A :=
  fun s h => forall h', hdisjoint h h' -> P s h' -> Q s (hunion h h').

Notation "P --* Q" := (wand P Q) (at level 70, right associativity).

Lemma wand_intro: forall {A:Type} (P Q R:assertion A),
  P ** Q -->> R  ->  P -->> Q --* R.
Proof.
  intros A P Q R IMP s h Ph h' DISJ Qh'.
  apply IMP. exists h, h'; auto.
Qed.

Lemma wand_cancel: forall {A:Type} {P Q:assertion A},
  P ** (P --* Q) -->> Q.
Proof.
  intros A P Q s h (h1 & h2 & Ph1 & Wh2 & D & U). subst h.
  assert (D': hdisjoint h2 h1) by (apply hdisjoint_sym; auto).
  rewrite hunion_comm by auto. apply Wh2; auto.
Qed.

Lemma wand_charact: forall {T:Type} (P Q:assertion T),
  (P --*Q) = (aexists (fun R => (P ** R -->> Q) //\\ R)).
Proof.
  intros T P Q; apply assertion_extensionality; intros s h; split.
- intros W. exists (P --* Q). split; auto. apply wand_cancel.
- intros (R & A & B) h' D Ph'.
  assert (D': hdisjoint h' h) by (apply hdisjoint_sym; auto).
  rewrite hunion_comm by auto. apply A. exists h', h; auto.
Qed.

Lemma wand_equiv: forall {A:Type} (P Q R:assertion A),
  (P -->> (Q --* R)) <-> (P ** Q -->> R).
Proof.
  intros; split; intros H.
- intros s h (h1 & h2 & Ph1 & Wh2 & D & U). subst h.
  apply H; auto.
- apply wand_intro; auto.
Qed.

Lemma wand_imp_l: forall {A:Type} (P P' Q:assertion A),
  (P' -->> P) -> (P --* Q -->> P' --* Q).
Proof.
  intros. intros s h W h' DISJ P'h'. apply W; auto.
Qed.

Lemma wand_imp_r: forall {A:Type} (P Q Q':assertion A),
  (Q -->> Q') -> (P --* Q -->> P --* Q').
Proof.
  intros. intros s h W h' DISJ Ph'. apply H; apply W; auto.
Qed.

Lemma wand_idem: forall {A:Type} (P:assertion A),
  emp -->> P --* P.
Proof.
  intros A P s h E. rewrite E. red. intros. rewrite hunion_empty. auto.
Qed.

Lemma wand_pure_l: forall {A:Type} (P: Prop) (Q:assertion A),
  P -> (pure P --* Q) = Q.
Proof.
  intros A P Q PP. apply assertion_extensionality. intros h; split.
- intros W. rewrite <- hunion_empty, hunion_comm by HDISJ. apply W. HDISJ. split; auto.
- intros Qh h' DISJ (Ph' & E). subst h'. rewrite hunion_comm, hunion_empty by HDISJ. auto.
Qed.

Lemma wand_curry: forall {A:Type} (P Q R:assertion A),
  (P ** Q --* R) = (P --* Q --* R).
Proof.
  intros; apply assertion_extensionality; intros h; split.
- intros W h1 D1 Ph1 h2 D2 Qh2. rewrite hunion_assoc. apply W. HDISJ. exists h1, h2; intuition auto. HDISJ.
- intros W h' D (h1 & h2 & Ph1 & Qh2 & D12 & U12). subst h'.
  rewrite <- hunion_assoc. apply W. HDISJ. auto. HDISJ. auto.
Qed.

Lemma wand_star: forall {A:Type} (P Q R:assertion A),
  ((P --* Q) ** R ) -->> (P --* (Q ** R)).
Proof.
  intros; intros s h (h1 & h2 & W1 & R2 & D & U). subst h. intros h' D' Ph'.
  exists (hunion h1 h'), h2; intuition auto.
  apply W1; auto. HDISJ.
  HDISJ.
  rewrite ! hunion_assoc. f_equal. apply hunion_comm. HDISJ.
Qed.

(** ** Precise assertions *)

(** An assertion is precise if "it unambiguously carves out an area of the heap"
   (in the words of Gotsman, Berdine, Cook, 2011). *)
(*
Definition precise (P: assertion) : Prop :=
  forall h1 h2 h1' h2',
  hdisjoint h1 h2 -> hdisjoint h1' h2' -> hunion h1 h2 = hunion h1' h2' ->
  P h1 -> P h1' -> h1 = h1'.

(** A parameterized assertion is precise if, in addition, the parameter
   is uniquely determined as well. *)

Definition param_precise {X: Type} (P: X -> assertion) : Prop :=
  forall x1 x2 h1 h2 h1' h2',
  hdisjoint h1 h2 -> hdisjoint h1' h2' -> hunion h1 h2 = hunion h1' h2' ->
  P x1 h1 -> P x2 h1' -> x1 = x2 /\ h1 = h1'.

Remark param_precise_precise:
  forall (X: Type) (P: X -> assertion),
  param_precise P -> forall x, precise (P x).
Proof.
  intros; red; intros. edestruct (H x x h1 h2 h1' h2'); eauto.
Qed.

Remark precise_param_precise:
  forall P, precise P -> param_precise (fun _ : unit => P).
Proof.
  intros; red; intros. split. destruct x1, x2; auto. eauto.
Qed.

Lemma pure_precise: forall P,
  precise (pure P).
Proof.
  unfold pure; intros; red; intros. destruct H2, H3. congruence.
Qed.

Lemma pure_param_precise: forall (X: Type) (P: X -> Prop),
  (forall x1 x2, P x1 -> P x2 -> x1 = x2) ->
  param_precise (fun x => pure (P x)).
Proof.
  unfold pure; intros; red; intros. destruct H3, H4. split. auto. congruence.
Qed. 

Lemma contains_param_precise: forall l,
  param_precise (fun v => contains l v).
Proof.
  unfold contains; intros; red; intros.
  assert (E: hunion h1 h2 l = hunion h1' h2' l) by congruence.
  cbn in E. subst h1 h1'. rewrite ! hupdate_same in E.
  replace x2 with x1 by congruence. auto.
Qed.

Lemma contains_precise: forall l v,
  precise (contains l v).
Proof.
  intros. apply param_precise_precise. apply contains_param_precise.
Qed.

Lemma aexists_precise: forall (X: Type) (P: X -> assertion),
  param_precise P -> precise (aexists P).
Proof.
  intros; red; intros. destruct H3 as (x1 & P1), H4 as (x2 & P2).
  eapply H; eauto.
Qed.

Lemma valid_precise: forall l,
  precise (valid l).
Proof.
  intros. apply aexists_precise. apply contains_param_precise.
Qed.

Lemma sepconj_param_precise: forall (X: Type) (P Q: X -> assertion),
  param_precise P -> (forall x, precise (Q x)) ->
  param_precise (fun x => P x ** Q x).
Proof.
  intros; red; intros. 
  destruct H4 as (h3 & h4 & P3 & Q4 & D & E). 
  destruct H5 as (h3' & h4' & P3' & Q4' & D' & E').
  subst h1 h1'.
  assert (x1 = x2 /\ h3 = h3'). 
  { apply H with (hunion h4 h2) (hunion h4' h2'); auto. HDISJ. HDISJ. 
    rewrite <- ! hunion_assoc. auto. }
  destruct H4. subst x2.
  assert (h4 = h4').
  { apply (H0 x1) with (hunion h3 h2) (hunion h3' h2'); auto. HDISJ. HDISJ.
    rewrite <- ! hunion_assoc.
    rewrite (hunion_comm h3) by HDISJ.
    rewrite (hunion_comm h3') by HDISJ.
    auto.
  }
  subst; auto.
Qed.

Lemma sepconj_precise: forall P Q,
  precise P -> precise Q -> precise (P ** Q).
Proof.
  intros.
  assert (param_precise (fun _ : unit => P ** Q)).
  { apply sepconj_param_precise. apply precise_param_precise; auto. auto. }
  apply param_precise_precise in H1. auto. exact tt.
Qed.

(** Distributivity laws for precise assertions. *)

Lemma sepconj_and_distr_1: forall P1 P2 Q,
  aand P1 P2 ** Q -->> aand (P1 ** Q) (P2 ** Q).
Proof.
  intros P1 P2 Q h (h1 & h2 & (P11 & P21) & Q2 & D & E); split; exists h1, h2; auto.
Qed.

Lemma sepconj_and_distr_2: forall P1 P2 Q,
  precise Q ->
  aand (P1 ** Q) (P2 ** Q) -->> aand P1 P2 ** Q.
Proof.
  intros P1 P2 Q PQ.
  rewrite (sepconj_comm P1), (sepconj_comm P2). 
  intros h ((h1 & h2 & Q1 & P12 & D & E) & (h1' & h2' & Q1' & P22 & D' & E')).
  assert (h1 = h1').
  { apply PQ with h2 h2'; auto. HDISJ. HDISJ. congruence. }
  subst h1'.
  assert (h2 = h2').
  { apply hunion_invert_r with h1; auto; congruence. }
  subst h2'.
  unfold aand; exists h2, h1; intuition auto. HDISJ. rewrite hunion_comm by HDISJ; auto.
Qed.

(** Self-conjunction law for precise assertions. *)

Lemma sepconj_self: forall P,
  precise P ->
  P ** P -->> P.
Proof.
  intros. intros h (h1 & h2 & P1 & P2 & D & E).
  assert (h1 = h2). { apply H with h2 h1; auto. HDISJ. apply hunion_comm; HDISJ. }
  subst h2.
  assert (h = h1). { apply heap_extensionality; intros l. rewrite E; cbn. destruct (h1 l); auto. }
  congruence.
Qed.

*) *)