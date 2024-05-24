
From CDF Require Import Heaps.
From Coq Require Import FunctionalExtensionality PropExtensionality.

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

(* TODO try autorewrite *)
Ltac heap := HUNION (3%nat); HDISJ; auto.

Ltac pre_ext :=
  apply functional_extensionality; intros s;
  apply functional_extensionality; intros h;
  apply propositional_extensionality.

Ltac post_ext :=
  apply functional_extensionality; intros r;
  pre_ext.
