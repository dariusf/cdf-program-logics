
From Coq Require Import ZArith Lia Bool List String Program.Equality.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Separation Seplog.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Section Flow.

Definition flow : Type := heap -> heap -> Prop.

Definition fexists {A: Type} (P: A -> flow) : flow :=
  fun h1 h2 => exists a: A, P a h1 h2.

(* Print assertion. *)
Definition freq (P: precond) : flow :=
  fun h1 h2 => exists h3 h4,
    h1 = hunion h3 h4 /\ hdisjoint h3 h4 /\ P h3 /\ h2 = h4.
    (* h3 is the part of the heap that is taken away by req,
    h4 is what is left *)

Definition fens (P: postcond) : flow :=
  fun h1 h2 => exists h3,
  exists r, (* TODO *)
    P r h3 /\ h2 = hunion h1 h3 /\ hdisjoint h1 h3.

Definition fempty : flow := fens (fun r h => True).

Definition fseq (f1 f2 : flow) : flow :=
  (* fun h1 h2 => exists h3, f1 h1 h3 /\ f2 h3 h2. *)
  fun h1 h2 => exists h3, f1 h1 h3 -> f2 h3 h2.

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
    forward (PURE n) (fens (fun res h => res = n))
  | fw_get: forall l v, 
    forward (GET l)
      (freq (fun h => h = hsingle l v) ;;
      fens (fun r h => h = hsingle l v /\ r = v))

  (* | fw_set: forall f l v, *)
    (* forward f (SET l v) f *)
  (* | fw_let: forall f e1 e2, *)
    (* forward f (LET e1 e2) f *)

  .

(* Example e1 : forall h1 h2, red (PURE 0, h1) (PURE 0, h2).
intros.
Qed. *)


(* Inductive a : flow -> com -> flow -> Prop := . *)

(* Inductive red: com * heap -> com * heap -> Prop := *)

(* red is a small step relation, soundness eventually needs to be proved for star red *)

Ltac inv H := inversion H; clear H; subst.

Theorem soundness : forall f c1 c2 h1 h2,
(* doesn't work for stuff that doesn't reduce, like pure *)
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
  unfold fseq.
  (* exists h2. *)
  (* intros hist. *)
  exists (hfree l h2).

  (* now partition the heap into h2 and emp,
  and assume there is h2[l:=v] *)
  unfold freq.
  intros [h3 [h4 [Hu [Hd [Hg He]]]]].
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
  rewrite He.
  rewrite hunion_comm.
  reflexivity.
  rewrite hdisjoint_sym; auto.
  unfold hsingle in *.
  pose proof hfree_hunion_hupdate as hh.
  rewrite hfree_hunion_hupdate.
  rewrite hdisjoint_sym; auto.
  auto.
Qed.

End Flow.
