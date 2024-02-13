
From Coq Require Import ZArith Lia Bool List String Program.Equality.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Sequences Separation Seplog.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Module Flow.

Definition flow : Type := heap -> heap -> Prop.

Definition fexists {A: Type} (P: A -> flow) : flow :=
  fun h1 h2 => exists a: A, P a h1 h2.

(* h3 is the part of the heap that is taken away by req,
   h4 is what is left *)
Definition freq (P: precond) (k : flow) : flow :=
  fun h1 h2 => exists h3 h4,
    h1 = hunion h3 h4 /\ hdisjoint h3 h4 /\ P h3
    ->
    k h4 h2.

Definition fens (P: postcond) : flow :=
  fun h1 h2 => exists h3,
  exists r, (* TODO *)
    P r h3 /\ h2 = hunion h1 h3 /\ hdisjoint h1 h3.

Definition fempty : flow := fens (fun r h => True).

Definition fseq (f1 f2 : flow) : flow :=
  fun h1 h2 => exists h3, f1 h1 h3 /\ f2 h3 h2.
  (* fun h1 h2 => exists h3, f1 h1 h3 -> f2 h3 h2. *)

Infix ";;" := fseq (at level 80, right associativity).

(* TODO disjunction *)

(* TODO functions *)

(* Definition fn (name : string) : flow :=
  fun _ => True. *)

(* forward rules. says how to produce a flow from a program *)
Inductive forward : com -> flow -> Prop :=
  | fw_skip:
    forward SKIP fempty
  | fw_pure: forall n,
    forward (PURE n) (fens (fun res => pure (res = n)))
  | fw_get: forall l v, 
    forward (GET l)
      (freq (contains l v)
      (fens (fun r => (r = v) //\\ contains l v)))


  (* | fw_set: forall f l v, *)
    (* forward f (SET l v) f *)
  (* | fw_let: forall f e1 e2, *)
    (* forward f (LET e1 e2) f *)

  .

(* this axiomatization of the models relation is not needed because of the semantic definitions above *)
(* Inductive satisfies : heap -> flow -> heap -> Prop :=
  | m_req: forall h1 h2 p k,
    satisfies h1 (freq p k) h2
  | m_ens: forall h1 h2 q,
    satisfies h1 (fens q) h2
. *)

(* Example e1 : forall h1 h2, red (PURE 0, h1) (PURE 0, h2).
intros.
Qed. *)


(* Inductive a : flow -> com -> flow -> Prop := . *)

(* Inductive red: com * heap -> com * heap -> Prop := *)

(* red is a small step relation, soundness eventually needs to be proved for star red *)

(* Ltac inv H := inversion H; clear H; subst. *)

Definition terminated (c: com) : Prop :=  c = SKIP.

Definition terminates (c1: com) (h1 h2: heap) : Prop :=
  exists c2, star red (c1, h1) (c2, h2) /\ terminated c2.

(* Definition goeswrong (c1: com) (h1: heap) : Prop :=
  exists c2 h2, star red (c1, h1) (c2, h2) /\ error c2 h2. *)

(* Fixpoint error (c: com) (s: heap) : Prop :=
  match c with
  | ASSERT b => beval b s = false
  | (c1 ;; c2) => error c1 s
  | _ => False
  end. *)


Theorem soundness : forall f c1 h1 h2 h3,
  forward c1 f ->
  terminates c1 h1 h2 ->
  f h1 h3 ->
  h2 = h3.
Proof.
admit.
Admitted.

Theorem soundness0 : forall f c1 c2 h1 h2,
(* TODO doesn't say anything about stuff that doesn't reduce, like pure *)
  red (c1, h1) (c2, h2) ->
  forward c1 f ->
  f h1 h2.
Proof.
  intros f c1 c2 h1 h2 Hr Hf.
  induction Hf.
  - inv Hr.
  - inv Hr.
  -
  (* inversion Hr. *)
  (* assert (fh = fempty). *)
  inv Hr.

  (* assuming we start in state h2 *)
  (* the intermediate states in sequencing are also h2 *)
  (* unfold fseq. *)
  (* exists h2. *)
  (* intros hist. *)

  (* now partition the heap into h2 and emp,
  and assume there is h2[l:=v] *)
  unfold freq.
  exists (hsingle l v).
  exists (hfree l h2).
  intros [h3 [h4 Hd]].
  subst.
  (* h2 is now called h0, and h4 is empty *)

  (* add another empty piece of heap, h3 *)
  unfold fens.
  exists (hsingle l v).
  exists v.
  subst.
  split.
  split; reflexivity.
  split.
  + rewrite hunion_comm; auto.
  + rewrite hdisjoint_sym; auto.
Qed.
(* Admitted. *)

End Flow.

Module Flow2.

  Definition flow : Type := heap -> heap -> bool -> Z -> Prop.

  Definition fexists {A: Type} (P: A -> flow) : flow :=
    fun h1 h2 p r =>
      exists a: A, P a h1 h2 p r.
    
  (* h3 is the part of the heap that is taken away by req,
    h4 is what is left *)
  (* Definition freq (P: precond) : flow :=
    fun h1 h2 p r =>
        (exists h3 h4, h1 = hunion h3 h4
          /\ hdisjoint h3 h4
          /\ P h3 /\ h2 = h4 /\ p = true)
        \/
        (forall h3 h4, h1 = hunion h3 h4
          /\ hdisjoint h3 h4
          /\ not (P h3) -> p = false). *)

  Definition freq (P: precond) : flow :=
    fun h1 h2 p r =>
        (exists h3 h4, h1 = hunion h3 h4
          /\ hdisjoint h3 h4
          /\ P h3 -> h2 = h4 /\ p = true)
        /\
        (not (exists h3 h4, h1 = hunion h3 h4
          /\ hdisjoint h3 h4
          /\ P h3) -> p = false).

  Definition fens (P: postcond) : flow :=
    fun h1 h2 p r =>
      exists h3,
        P r h3
        /\ h2 = hunion h1 h3
        /\ hdisjoint h1 h3.

  Definition fempty : flow := fens (fun r h => h = hempty).

  Definition fseq (f1 f2 : flow) : flow :=
    fun h1 h2 p r =>
        (exists h3 r1,
          f1 h1 h3 true r1 /\ f2 h3 h2 p r)
        \/ f1 h1 h2 false r.

  Infix ";;" := fseq (at level 80, right associativity).

  Example ex_take_put_back : forall x v r, (freq (contains x v) ;; fens (fun r => contains x v)) (hupdate x v hempty) (hupdate x v hempty) true r.
  Proof.
    intros.
    unfold fseq.
    left.
    exists hempty. exists 1.
    split.
    - unfold freq.
    left.
    exists (hupdate x v hempty).
    exists hempty.
    split.
    rewrite <- hunion_comm.
    rewrite hunion_empty.
    reflexivity.
    rewrite hdisjoint_sym.
    apply hdisjoint_empty.
    split.
    HDISJ.
    split.
    unfold contains.
    reflexivity.
    split; auto.
    - unfold fens.
    exists (hupdate x v hempty).
    repeat split.
    rewrite hunion_empty.
    reflexivity.
    apply hdisjoint_empty.
  Qed.

  Example ex_vacuous_req : forall x v r, (freq (contains x v)) (hempty) (hupdate x v hempty) false r.
  Proof.
    intros.
    unfold freq.
    (* taking right branch is easy, but soundness seems difficult as we can always take it *)
    (* right.
    intros.
    reflexivity. *)
    left.
    (* cannot prove if i take the left branch *)
    exists hempty.
    exists hempty.
    repeat split.
    rewrite hunion_empty.
    reflexivity.
    apply hdisjoint_empty.
  Abort.

  Example ex_take : forall x v r, (freq (contains x v)) (hupdate x v hempty) (hempty) false r.
  Proof.
    intros.
    unfold freq.
    left.
    exists (hupdate x v hempty).
    exists hempty.
    repeat split.
    rewrite hunion_comm.
    rewrite hunion_empty.
    reflexivity.
    HDISJ.
    HDISJ.
    (* we can't say false if we take the left branch *)
  Abort.

  Example ex_vacuous_req_wrong : forall x v r, (freq (contains x v)) (hupdate x v hempty) (hempty) false r.
  Proof.
    intros.
    unfold freq.
    right.
    (* we can always take the right branch though *)
    intros.
    reflexivity.
  Qed.

  Example ex_vacuous_seq : forall x v r, (freq (contains x v) ;; fens (fun r => contains x v)) (hempty) (hupdate x v hempty) false r.
  Proof.
    intros.
    unfold fseq.
    right.
    unfold freq.
    right.
    intros.
    reflexivity.
  Qed.

  Inductive forward : com -> flow -> Prop :=
    | fw_skip:
      forward SKIP fempty
    | fw_pure: forall n,
      forward (PURE n) (fens (fun res => pure (res = n)))
    | fw_get: forall l v, 
      forward (GET l)
        (freq (contains l v) ;;
        (fens (fun r => (r = v) //\\ contains l v)))
        .

  Definition terminated (c: com) : Prop :=  c = SKIP.

  Definition terminates (c1: com) (h1 h2: heap) : Prop :=
    exists c2, star red (c1, h1) (c2, h2) /\ terminated c2.

  (* Definition goeswrong (c1: com) (h1: heap) : Prop :=
    exists c2 h2, star red (c1, h1) (c2, h2) /\ error c2 h2. *)

  (* Fixpoint error (c: com) (s: heap) : Prop :=
    match c with
    | ASSERT b => beval b s = false
    | (c1 ;; c2) => error c1 s
    | _ => False
    end. *)

Ltac destr H :=
  match type of H with
  | ex _ => 
    let L := fresh "e" in
    let R := fresh "H" in
    destruct H as [L R]; destr R
  | _ /\ _ => 
    let L := fresh "L" in
    let R := fresh "R" in
    destruct H as [L R]; destr L; destr R
  | _ => idtac
  end.

  Theorem soundness : forall c1 h1 h2 h3 r p f,
    forward c1 f ->
    terminates c1 h1 h2 ->
    f h1 h3 p r ->
    h2 = h3.
  Proof.
    (* intros c1. *)
    (* induction c1; intros. *)
    intros c1 h1 h2 h3 r p f Hf.
    induction Hf; intros Hr Hs.
    -
      (* skip *)
    {
    inv Hr.
    destruct H.
    inv H.
    -
    (* skip has terminated *)
      inv H0.
      unfold fempty in Hs.
      unfold fens in Hs.
      destruct Hs as [h0 [H1 [H2 H3]]].
      subst.
      rewrite hunion_comm.
      rewrite -> hunion_empty.
      auto.
      rewrite hdisjoint_sym.
      auto.
    -
    (* skip reduces *)
    inv H1.
    }
    -
    (* pure *)
    {
      inv Hr.
      destruct H. inv H.
      -
      (* pure terminates *)
      unfold fens in Hs.
      destruct Hs as [h0 [H1 [H2 H3]]].
      unfold pure in H1.
      destruct H1.
      subst.
      rewrite hunion_comm.
      rewrite hunion_empty.
      auto.
      apply hdisjoint_empty.
      -
      (* pure takes steps *)
      inv H1.
    }
    -
    (* deref *)
    {
    inv Hr.
    destruct H.
    inv H.
    -
    (* get has terminated *)
    inv H0.
    - {
    (* get reduces *)
    inv H1.
    inv H2.
    - {
    (* pure has terminated *)
    unfold fseq in Hs.
    destruct Hs.
    - {
      (* seq does not vacuously succeed early *)
      destr H.
      unfold freq in L.
      destr L.
      destruct L.
      - destr H. unfold fens in R. destr R. subst.
      unfold pureconj in L3. destruct L3. subst.
      unfold contains in H1.
      unfold contains in L1.
      subst.
      rewrite hunion_comm; auto.
      -
      pose proof (H h2 h3).
      destr H1.
      (* inv R0. *)
      admit.
    }
    -
      (* seq vacuously succeeds early *)
      { inv H0.
      inv H.
      destruct H0.
      destruct H.
      - destr H. inv R0.
      - admit.
      }
    } 
    -
    (* pure reduces *)
    inv H.
}
    }
  (* Qed. *)
  Admitted.

End Flow2.