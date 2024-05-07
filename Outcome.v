
From Coq Require Import ZArith Lia Bool List String Program.Equality.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Common Sequences.
From Coq Require Import ssreflect ssrfun ssrbool.

Local Open Scope string_scope.
Local Open Scope core_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Ltac inv H := inversion H; clear H; subst.

(* https://github.com/mattam82/Coq-Equations/blob/main/theories/Init.v#L148 *)
Ltac forward_gen H tac :=
  match type of H with
  | forall (_ : ?X), _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

(* https://softwarefoundations.cis.upenn.edu/plf-current/LibTactics.html *)
Ltac get_head E :=
  match E with
  | ?E' ?x => get_head E'
  | _ => constr:(E)
  end.

Ltac apply_to_head_of E cont :=
  let go E :=
    let P := get_head E in cont P in
  match E with
  | forall _,_ => intros; apply_to_head_of E cont
  | ?A = ?B => first [ go A | go B ]
  | ?A => go A
  end.
Ltac unfolds_base :=
  match goal with |- ?G =>
   apply_to_head_of G ltac:(fun P => unfold P) end.

Tactic Notation "unfolds" :=
  unfolds_base.

Ltac unfolds_in_base H :=
  match type of H with ?G =>
   apply_to_head_of G ltac:(fun P => unfold P in H) end.
Tactic Notation "unfolds" "in" hyp(H) :=
  unfolds_in_base H.


Section RC.
  Local Open Scope nat_scope.
  Inductive resources := rb (l:nati) (u:nati).

  Definition resources_le (b a:resources) : Prop :=
    match b, a with
    | rb bl bu, rb al au =>
      (al <= bl /\ bu <= au)%nati
    end.

  Declare Scope resources_scope.
  Delimit Scope resources_scope with resources.
  Notation "a <= b" := (resources_le a b) : resources_scope.
  (* Bind Scope resources_scope with resources. *)

  Lemma resources_largest : forall r, (r <= (rb 0 inf))%resources.
  Proof.
    rewrite /resources_le => r.
    destruct r.
    rewrite /nati_le.
    split.
    destruct l; intuition lia.
    destruct u; intuition lia.
  Qed.

  (* executions allowed by a can be decomposed into executions requiring b,
    followed by executions requiring c.
    informally, like a - b = c *)
  Definition resources_split (a b c:resources) : Prop :=
    match a, b, c with
    | rb al au, rb bl bu, rb cl cu =>
      (* cannot take more resources than available *)
      (bu <= au ->
      (* could lead to cl > cu *)
      al + bu <= au + bl ->
      (* these conditions ensure that c is the largest resource consumption *)
      (forall x, x + bl >= al -> cl <= x) /\ (* minimality *)
      (forall x, x + bu <= au -> cu >= x) /\ (* maximality *)
      (* ub must be less (as we can't take more than is available),
        lb must be greater (as we must consume as least as much as required) *)
      cl + bl >= al /\ cu + bu <= au)%nati
    end.
  (* https://stackoverflow.com/questions/50445983/minimum-in-non-empty-finite-set *)

  Section Constructive.

    Definition nati_min_minus (a b:nati) : nati :=
      match a, b with
      | n a, n b => n (a-b)%nat
      | n _, inf => 0
      | inf, n _ => inf
      | inf, inf => 0
      end.

    Definition nati_max_minus (a b:nati) : nati :=
      match a, b with
      | n a, n b => n (a-b)%nat
      | n _, inf => 0
      | inf, n _ => inf
      | inf, inf => inf
      end.

    Definition resources_split_constr (a b c:resources) : Prop :=
      match a, b, c with
      | rb al au, rb bl bu, rb cl cu =>
        (* cannot take more resources than available *)
        (bu <= au ->
        (* lead to cl > cu *)
        al + bu <= au + bl ->
          cl = nati_min_minus al bl /\ cu = nati_max_minus au bu
        )%nati
          (* match al, au, bl, bu with
          | n al, n au, n bl, n bu => cl = al - bl /\ cu = au - bu
          | n al, n au, n bl, inf => False (* first condition *)
          | n al, n au, inf, n bu => False (* not wf *)
          | n al, n au, inf, inf => False (* first condition *)
          | n al, inf, n bl, n bu => cl = al - bl /\ cu = inf
          | n al, inf, n bl, inf => cl = al - bl /\ cu = inf
          | n al, inf, inf, n bu => False (* not wf *)
          | n al, inf, inf, inf => cl = inf /\ cu = inf
          | inf, n au, n bl, n bu => False (* not wf *)
          | inf, n au, n bl, inf => False (* not wf *)
          | inf, n au, inf, n bu => False (* not wf *)
          | inf, n au, inf, inf => False (* not wf *)
          | inf, inf, n bl, n bu => cl = inf /\ cu = inf
          | inf, inf, n bl, inf => cl = inf /\ cu = inf
          | inf, inf, inf, n bu => False (* not wf *)
          | inf, inf, inf, inf => cl = 0 /\ cu = inf
          end)%nati *)
      end.

    (* Lemma aaa : forall a b c,
      (forall x : nati, (x + b >= a)%nati -> (x >= c)%nati)
      /\ (c + b >= a)%nati
      <->
      c = nati_min_minus a b.
    Proof.
      intros.
      split; intros.
      - 
        destruct H.
        unfold nati_min_minus.
        destruct a.
        destruct b.
        destruct c.
        unfold nati_plus in H0.
        unfold nati_le in H0.
        inversion H0.
        + rewrite Nat.add_sub.
        reflexivity.
        + 

        Search ((_ + _) - _).
        (* rewrite Nat.add *)
        Print Init.Nat.sub.
        Unset Printing Notations.
        simpl.
        lia.
        simpl.

        Unset Printing Coercions.
        rewrite <- H0.

        lia.
        (* rewrite <- H0. *)
        
        (* 
        (* specialize (H l1). *)
        unfold nati_plus in H0.
        destruct l1.
        admit.
        rewrite H0.
        Unset Printing Notations. *)
        (* rewrite <- H0.
        lia.
        rewrite <- H0.
        lia.
        rewrite <- H0.

        lia. *)
      admit.
      - admit.
    Admitted.
 *)


    Lemma nati_le_antisymm : forall n m,
      (n <= m -> m <= n -> n = m)%nati.
    Proof.
      intros n m H1 H2.
      unfold nati_le in H1.
      unfold nati_le in H2.
      destruct n; destruct m.
      - f_equal.
        apply Nat.le_antisymm.
        auto. auto.
      - easy.
      - easy.
      - easy.
    Qed.

    Lemma resources_split_equiv : forall a b c,
      resources_split a b c <-> resources_split_constr a b c.
    Proof.
      split; intros.
      - destruct a. destruct b. destruct c.
        unfold resources_split in H.
        unfold resources_split_constr.
        intros.
        forward H by auto.
        forward H by auto.
        destruct H as [Hmin [Hmax [Hl Hu]]].
        split.
        unfold nati_min_minus.
        destruct l.
        destruct l0.
        rewrite nati_plus_ge in Hl.
        (* TODO split should talk about how the lower bounds are related? *)
        admit.
        specialize (Hmin (n - n0)).
        forward Hmin by simpl; lia.
        pose proof (nati_le_antisymm _ _ Hl Hmin).
        easy.
    Abort.
  End Constructive.

  Section Examples.

    Example e1_split : resources_split
      (rb 0 3) (rb 0 2) (rb 0 1).
    Proof. unfold resources_split. intros. intuition.
    - now rewrite nati_plus_0 in H1.
    - rewrite nati_plus_le in H1; try lia.
      now simpl in H1.
    - now simpl.
    - now simpl.
    Qed.

    (* cannot take more than available *)
    Example e1_split_f : resources_split
      (rb 0 3) (rb 0 2) (rb 0 2).
    Proof. unfold resources_split. intros. intuition.
    - now rewrite nati_plus_0 in H1.
    - rewrite nati_plus_le in H1; try lia.
      simpl in H1.
    Abort.

    (* given inf, we can have as much remaining as we want *)
    Example e2_split : resources_split
      (rb 0 inf) (rb 0 2) (rb 0 inf).
    Proof. unfold resources_split. intros. intuition.
      - now rewrite nati_plus_0 in H1.
      - now rewrite nati_le_inf in H1.
      - now simpl.
    Qed.

    Example e3_split : resources_split
      (rb 0 inf) (rb 0 2) (rb 0 inf).
    Proof. unfold resources_split. intros. intuition.
      - now rewrite nati_plus_0 in H1.
      - now rewrite nati_le_inf in H1.
      - now simpl.
    Qed.

    (* but not as little *)
    Example e5_split : resources_split
      (rb 0 inf) (rb 0 2) (rb 0 1).
    Proof. unfold resources_split. intros. intuition.
      - now rewrite nati_plus_0 in H1.
      - rewrite nati_le_inf in H1.
    Abort.

    Example e6_split : resources_split
      (rb 0 inf) (rb 0 inf) (rb 0 0).
    Proof. unfold resources_split. intros. intuition.
      - now rewrite nati_plus_0 in H1.
      - rewrite nati_le_inf in H1.
    Abort.

    (* we can even extract inf and have inf remaining *)
    Example e4_split : resources_split
      (rb 0 inf) (rb 0 inf) (rb 0 inf).
    Proof. unfold resources_split. intros. intuition.
      - now rewrite nati_plus_0 in H1.
      - now rewrite nati_le_inf in H1.
      - now simpl.
    Qed.

    (* but not nothing *)
    Example e7_split : resources_split
      (rb 0 inf) (rb 0 inf) (rb 0 0).
    Proof. unfold resources_split. intros. intuition.
      - now rewrite nati_plus_0 in H1.
      - rewrite nati_le_inf in H1.
    Abort.

  End Examples.

  (* Lemma resources_split_undefined : forall a b c al au bl bu,
    a = rb al au ->
    b = rb bl bu ->
    (bu > au)%nati ->
    not (resources_split a b c).
  Proof.
    unfold not; intros; subst.
    destruct H1.
    apply: H0.

    unfold resources_split in H2; destruct c.

    unfold nati_le in H.
    destruct au.
    destruct bu.
    induction H.
    - reflexivity.
    -

    destruct au.
    destruct bu.
    f_equal.
  Admitted. *)

  Definition rc_assert := resources -> Prop.
  Definition rc (l:nati) (u:nati) : rc_assert :=
    fun r =>
      match r with | rb ml mu => ml = l /\ mu = u end.

  Definition mayloop := rc 0 inf.
  Definition loop := rc inf inf.
  Definition term x := rc 0 x. (* TODO *)

  Definition rc_entail (a b:rc_assert) : Prop :=
    forall r, a r -> b r.
  Definition rc_and (a b:rc_assert) : rc_assert :=
    fun r => a r /\ b r.
  Definition rc_equiv (a b:rc_assert) : Prop :=
    forall r, a r <-> b r.
  Definition rc_false : rc_assert := fun r => False.

  (* triangle *)
  Definition rc_split (a b:rc_assert) : rc_assert := fun r =>
    forall r1 r2,
    resources_split r r1 r2 ->
    a r1 /\ b r2.

  Definition rc_entail_frame (a b c:rc_assert) : Prop :=
    rc_entail a (rc_split b c).

  (* \vdash \blacktriangleright *)
  Notation "a ⊢ b ▶ c" := (rc_entail_frame a b c) (at level 100) : resources_scope.

  Lemma aa : forall l1 l0,
    (forall x : nati, (0 <= x + l0)%nati -> (l1 <= x)%nati) ->
    (0 <= l1 + l0)%nati.
  Proof.
    intros.
    specialize (H 0).
    simpl.
    destruct (l1 + l0)%nati.
    lia.
    easy.
  Qed.

  Lemma aa1 : forall (c b a:nati),
    (a > b)%nati ->
    (forall x, (a <= x + b)%nati -> (c <= x)%nati) ->
    (a <= c + b)%nati ->
    c = nati_min_minus a b.
  Proof.
    intros c b a H H0 H1.
    unfold nati_min_minus.
    destruct a as [na|]; destruct b as [nb|]; destruct c as [nc|].
    - (* show that it's also bounded from above by na-nb *)
    specialize (H0 (na - nb)).
    rewrite nati_plus_ge in H1.
    unfold nati_le in H. destruct H. inversion H.
    + exfalso. apply H1. f_equal. easy.
    + rewrite H3. inversion H2; lia.
    + forward H0 by simpl; lia.
    pose proof (nati_le_antisymm (na-nb) nc H1 H0).
    symmetry. easy.

    - simpl in *.
    specialize (H0 na).
    simpl in H0.
    forward H0. lia. easy.
    (* vacuously true as inf isn't smallest *)
    - now simpl in *.
    - now simpl in *.
    - now simpl in *.
    - now simpl in *.
    - now simpl in *.
    - now simpl in *.
  Qed.

  Lemma aa2 : forall (c b a:nati),
    (a >= b)%nati ->
    (forall x, (a <= x + b)%nati -> (c <= x)%nati) ->
    (a <= c + b)%nati ->
    c = nati_min_minus a b.
  Proof.
    intros c b a H H0 H1.
    unfold nati_min_minus.
    destruct a as [na|]; destruct b as [nb|]; destruct c as [nc|].
    - (* show that it's also bounded from above by na-nb *)
    specialize (H0 (na - nb)).
    rewrite nati_plus_ge in H1.
    unfold nati_le in H.
    unfold ge.
    assumption.
    + forward H0 by simpl; lia.
    pose proof (nati_le_antisymm (na-nb) nc H1 H0).
    symmetry. easy.

    - simpl in *.
    specialize (H0 na).
    simpl in H0.
    forward H0. lia. easy.
    (* vacuously true as inf isn't smallest *)
    - now simpl in *.
    - now simpl in *.
    - now simpl in *.
    - now simpl in *.
    - simpl in *.
    specialize (H0 0).
    simpl in *.
    forward H0 by easy.
    inversion H0.
    easy.
    - simpl in *.
    specialize (H0 0).
    simpl in *.
    easy.
  Qed.

  Lemma inf_greatest : forall a, (a <= inf)%nati.
  Proof.
    intros.
    unfold nati_le. destruct a; easy.
  Qed.

  Lemma l2 : rc_entail_frame loop loop mayloop.
  Proof.
    unfold rc_entail_frame.
    unfold rc_entail.
    unfold rc_split.
    intros.
    unfold resources_split in H0. destruct r. destruct r1. destruct r2.
    destruct H.
    subst.
    forward H0 by unfold nati_le; destruct u0; easy.
    forward H0 by rewrite nati_le_inf_r; rewrite nati_le_inf; easy.
    destruct H0 as [Hmin [Hmax [Hl Hu]]].

    (* we need to determine these values *)
    unfold loop.
    unfold mayloop.
    unfold rc.

    (* how? *)
    (* assert (forall a, a <= inf)%nati. admit. *)
    pose proof (inf_greatest l0) as H0.
    pose proof (aa2 _ _ _ H0 Hmin Hl) as H1.
    simpl in H1.

    destruct l0.

    admit. (* find contradiction if l0 is finite *)
  Abort.

  Lemma l1 : rc_entail_frame mayloop mayloop mayloop.
  Proof.
    unfold rc_entail_frame.
    unfold rc_entail.
    unfold rc_split.
    intros.
    unfold resources_split in H0. destruct r. destruct r1. destruct r2.
    destruct H.
    subst.
    forward H0 by unfold nati_le; destruct u0; easy.
    forward H0 by rewrite nati_le_inf_r; rewrite nati_le_inf; easy.
    destruct H0 as [Hmin [Hmax [Hl Hu]]].

    (* specialize (Hmin 0). *)
    (* simpl in Hmin. *)
    (* destruct l0. *)

    unfold mayloop.
    unfold rc.

    assert (l0 <= 0)%nati.
    unfold nati_le.

    admit.
    pose proof (aa2 _ _ _ H Hmin Hl).
    simpl in H0.
    destruct l0.
    subst.
    simpl in *.

    (* intuition. *)
    (* specialize (Hmin l0). *)
    (* apply aa1. *)


    (* split. *)
    (* TODO *)
  Abort.

  Lemma rc_eq : forall al au bl bu,
    rc_entail (rc al au) (rc bl bu) <->
    al = bl /\ au = bu.
  Proof.
    intros.
    split.
    - intros. unfold rc_entail in H. unfold rc in H. specialize (H (rb al au)).
      simpl in H.
      now apply H.
    - intros. destruct H. subst. unfold rc_entail. intros. assumption.
  Qed.

  Lemma rc_eq1 : forall al au bl bu,
    (rc_equiv (rc_and (rc al au) (rc bl bu)) (rc al au)) <->
    al = bl /\ au = bu.
  Proof.
    move=> al au bl bu.
    split; intros.
    - unfold rc_equiv in H.
    unfold rc_and in H.
    unfold rc in H.
    specialize (H (rb al au)).
    destruct H.
    forward H0 by intuition.
    destruct H0.
    auto.
    - destruct H.
    unfold rc_equiv.
    unfold rc_and.
    unfold rc.
    subst.
    intros.
    intuition.
  Qed.

  Lemma rc_contradiction : forall al au bl bu,
    al <> bl \/ au <> bu ->
      rc_equiv (rc_and (rc al au) (rc bl bu)) rc_false.
  Proof.
    move=> al au bl bu.
    case=>[H|H].
    - rewrite /rc_equiv /rc_and /rc /rc_false => r.
    intuition.
    destruct r.
    (* move: H1 H2 => [? ?] [? ?]. *)
    destruct H1; destruct H2.
    congruence.
    - rewrite /rc_equiv /rc_and /rc /rc_false => r.
    destruct r.
    intuition.
    congruence.
  Qed.

  (* Inductive rea := Term | MayLoop | Loop. *)
  (* resource assertion *)

End RC.

Definition val := Z.
(* Inductive val := int (i:Z) | ni (n:nati). *)

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

  Definition model := store -> resources -> Prop.

  Definition assertion := store -> Prop.
  Definition rassertion := store -> store -> Prop.
  Definition precond := assertion.
  Definition postcond := val -> rassertion.

  (* Inductive lar := LR (d:precond) (r:rea). *)
  (* logic and resource *)

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

    | div_pif_then : forall s x e1 e2,
      diverges s e1 ->
      s x = Some 0 ->
      diverges s (pif x e1 e2)

    | div_pif_else : forall s x e1 e2,
      diverges s e2 ->
      s x <> Some 0 ->
      diverges s (pif x e1 e2)

    .

  Definition triple (P: precond) (e: expr) (Q: outcome) : Prop :=
    forall ok er nt r s s1,
      Q = ok_er_nt ok er nt ->
      P s ->
           (eval[ s, e ] => [ s1, Some r ] -> ok r s s1)
        /\ (eval[ s, e ] => [ s1, None ] -> er s)
        /\ (diverges s e -> nt s).

  Definition rand (P:assertion) (Q:rassertion) : rassertion :=
    fun old s => P old /\ Q old s.

  Lemma f_pconst : forall v p,
    triple p (pconst v) (ok_only (fun r => rand p (fun old s => r = v))).
  Proof.
    intros.
    unfold triple.
    intros.
    unfold ok_only in H; injection H; clear H; intros.
    repeat split; intros.
    - inversion H3; subst; clear H3.
      unfold rand; easy.
    - inversion H3.
    - inversion H3.
  Qed.

  Lemma f_var : forall x p,
    triple p (pvar x) (ok_only (fun r => rand p (fun old s => Some r = old x))).
  Proof.
    intros.
    unfold triple.
    intros.
    unfold ok_only in H; injection H; clear H; intros.
    repeat split; intros.
    - inversion H3; subst; clear H3.
      unfold rand; easy.
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

  Definition aand (p1 p2:assertion) : assertion :=
    fun s => p1 s /\ p2 s.

  Lemma f_pif : forall x e1 e2 p s1a s1b s1c s2a s2b s2c,
    triple (aand p (fun s => s x = Some 0)) e1 (ok_er_nt s1a s1b s1c) ->
    triple (aand p (fun s => s x <> Some 0)) e2 (ok_er_nt s2a s2b s2c) ->
    triple p (pif x e1 e2) (ok_er_nt
      (fun r => fun old s => s1a r old s \/ s2a r old s)
      (fun s => s1b s \/ s2b s)
      (fun s => s1c s \/ s2c s)).
  Proof.
    intros.
    unfold triple.
    intros.
    injection H1; clear H1; intros.
    repeat split; intros.
    - inv H5.
      + unfold triple in H.
        specialize (H s1a s1b s1c r s s1).
        unfold aand in H.
        forward H by reflexivity. forward H by intuition.
        destruct H as [Hok [_ _]].
        forward Hok by assumption.
        now left.
      + unfold triple in H0.
        assert (ok_er_nt s2a s2b s2c = ok_er_nt s2a s2b s2c). { reflexivity. }
        unfold aand in H0. assert (p s /\ s x <> Some 0). { auto. }
        specialize (H0 s2a s2b s2c r s s1 H1 H3).
        destruct H0 as [Hok [_ _]].
        specialize (Hok H12).
        now right.
    - inv H5.
      + unfold triple in H.
        assert (ok_er_nt s1a s1b s1c = ok_er_nt s1a s1b s1c). { reflexivity. }
        unfold aand in H. assert (p s /\ s x = Some 0). { auto. }
        specialize (H s1a s1b s1c 0 s s1 H1 H3).
        destruct H as [_ [Her _]].
        specialize (Her H12).
        now left.
      + unfold triple in H0.
        assert (ok_er_nt s2a s2b s2c = ok_er_nt s2a s2b s2c). { reflexivity. }
        unfold aand in H0. assert (p s /\ s x <> Some 0). { auto. }
        specialize (H0 s2a s2b s2c 0 s s1 H1 H3).
        destruct H0 as [_ [Her _]].
        specialize (Her H12).
        now right.
    - inv H5.
      + unfold triple in H.
        assert (ok_er_nt s1a s1b s1c = ok_er_nt s1a s1b s1c). { reflexivity. }
        unfold aand in H. assert (p s /\ s x = Some 0). { auto. }
        specialize (H s1a s1b s1c 0 s s1 H1 H3).
        destruct H as [_ [_ Hnt]].
        specialize (Hnt H9).
        now left.
      + unfold triple in H0.
        assert (ok_er_nt s2a s2b s2c = ok_er_nt s2a s2b s2c). { reflexivity. }
        unfold aand in H0. assert (p s /\ s x <> Some 0). { auto. }
        specialize (H0 s2a s2b s2c 0 s s1 H1 H3).
        destruct H0 as [_ [_ Hnt]].
        specialize (Hnt H9).
        now right.
  Qed.

    (* TODO let *)

    (* TODO call *)
    (* | f_pcall : forall y b f c r x d,
      fenv f = Some (fn y b) ->
      forward (LR d r) (pcall f x) (ok_only (fun r => aand s (fun s => r = c))) *)

End Bigstep.