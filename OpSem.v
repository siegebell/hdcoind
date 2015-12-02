Require Import Coq.Program.Syntax.
Require Export ZArith.
Require Import Coq.Program.Basics.
Require Import SetoidTactics.
Require Import SetoidClass.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.

Require Import HDI.Util.
Require Import HDI.Syntax.
Require Import HDI.Heap.

Local Open Scope Z.


Inductive step (h: heap) : stmt -> heap -> stmt -> Prop :=
  | s_read: forall a v,
    h a = Some v ->
    step h (act (read a)) h (ret v)
  | s_write: forall v0 a v h',
    h a = Some v0 ->
    h' = upd_heap h a v ->
    step h (act (write a v)) h' (ret 1)
  | s_bind1: forall s k h' s',
    step h s h' s' ->
    step h (bind s k) h' (bind s' k)
  | s_bind_ret: forall v k,
    step h (bind (ret v) k) h (k v).

Inductive step_star (h: heap) (s: stmt) : heap -> stmt -> Prop :=
  | step_nil:
    step_star h s h s
  | step_cons: forall h' s' h'' s'',
    step h s h' s' ->
    step_star h' s' h'' s'' ->
    step_star h s h'' s''.

Hint Constructors step : safe.


  Lemma step_heap_equiv1: forall h1 h2 s h1' s',
    heap_equiv h1 h2 ->
    step h1 s h1' s' ->
    exists h2',
      step h2 s h2' s' /\ heap_equiv h1' h2'.
  Proof.
    intros.
    induction H0; subst; eauto with safe;
      try solve [erewrite heap_lookup_equiv in *; eauto using upd_heap_equiv with safe].
    destruct IHstep as [h2'[??]]; eauto with safe.
  Qed.

  Lemma step_heap_equiv2: forall h1 h2 s h2' s',
    heap_equiv h1 h2 ->
    step h2 s h2' s' ->
    exists h1',
      step h1 s h1' s' /\ heap_equiv h1' h2'.
  Proof.
    intros.
    symmetry in H.
    edestruct step_heap_equiv1 as [h1'[??]]; eauto.
    symmetry in H2; eauto.
  Qed.

  Lemma step_deterministic: forall h s h1' h2' s1' s2',
    step h s h1' s1' ->
    step h s h2' s2' ->
    h1' = h2' /\ s1' = s2'.
  Proof.
    intros ? ? ? ? ? ? Hstep1 Hstep2.
    revert h2' s2' Hstep2.
    induction Hstep1; intros; inversion Hstep2;
      instantiate;
      repeat match goal with
      | H1: act ?a1 = act ?a2 |- _ => inversion H1; try (subst a1 || subst a2); clear H1
      | H1: read ?a1 = read ?a2 |- _ => inversion H1; try (subst a1 || subst a2); clear H1
      | H1: write ?a1 ?v1 = write ?a2 ?v2 |- _ => inversion H1; try (subst a1 || subst a2); try (subst v1 || subst v2); clear H1
      | H1: bind ?s1 ?k1 = bind ?s2 ?k2 |- _ => inversion H1; try (subst s1 || subst s2); try (subst k1 || subst k2); clear H1
      | H1: step _ (ret _) _ _ |- _ => solve[inversion H1]
      | _ => progress subst
      | _ => reflexivity
      | |- _/\_ => split; [ reflexivity | ]
      | _ => congruence
      end.
    edestruct IHHstep1; eauto; subst; auto.
  Qed.

