Require Import Coq.Program.Syntax.
Require Export ZArith.
Require Import Coq.Program.Basics.
Require Import SetoidTactics.
Require Import SetoidClass.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.

Require Import HDI.Util.

Local Open Scope Z.

Definition heap:= Z -> option Z.

Definition upd_heap (h: heap) (a:Z) (v:Z) := fun a' =>
  if a' =? a then
    Some v
  else
    h a'.

Definition heap_empty : heap:= fun a => None.

Definition heap_singleton a v : heap:= fun a' =>
  if a' =? a then Some v else None.

Definition heap_join (h1 h2: heap) : heap:= fun a =>
  match h1 a with
  | Some v1 => Some v1
  | None => h2 a
  end.

Definition heap_equiv (h1 h2: heap):= forall a, h1 a = h2 a.

Instance heap_equiv_eq: Equivalence heap_equiv.
Proof.
  unfold heap_equiv; constructor; hnf; simpl; intros; firstorder congruence.
Qed.

Instance heap_setoid: Setoid heap :=
  {| equiv:= heap_equiv |}.

Global Instance heap_equiv_sub_equiv: subrelation heap_equiv equiv.
Proof. firstorder. Qed.

Opaque heap_setoid.

  Lemma heap_singleton_lookup: forall a v,
    (heap_singleton a v) a = Some v.
  Proof.
    unfold heap_singleton; intros.
    rewrite Z.eqb_refl.
    reflexivity.
  Qed.

  Lemma upd_heap_lookup: forall h a v,
    (upd_heap h a v) a = Some v.
  Proof.
    unfold upd_heap; intros.
    rewrite Z.eqb_refl.
    reflexivity.
  Qed.

  Lemma heap_lookup_equiv: forall h1 h2 a,
    heap_equiv h1 h2 ->
    h1 a = h2 a.
  Proof. intuition auto. Qed.

  Lemma upd_heap_equiv: forall h1 h2 a v,
    heap_equiv h1 h2 ->
    heap_equiv (upd_heap h1 a v) (upd_heap h2 a v).
  Proof.
    unfold upd_heap, heap_equiv; intros.
    case_eq (a0 =? a); auto.
  Qed.

  Add Parametric Morphism : upd_heap
    with signature equiv ==> eq ==> eq ==> equiv
    as upd_heap_m.
  Proof.
    intros; eapply upd_heap_equiv; eauto.
  Qed.


