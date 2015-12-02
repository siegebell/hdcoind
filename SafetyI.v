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
Require Import HDI.OpSem.
Require Import HDI.Bisimulation.
Require Import HDI.Safety.

Local Open Scope stmt.


  CoInductive safeI (I: heap->stmt->Prop) (h: heap) : stmt -> Prop :=
  | safeI_ret: forall v,
    safeI I h (ret v)
  | safeI_exists_step: forall s,
    (exists h' s',
      step h s h' s' /\ (I h' s' \/ safeI I h' s')) ->
    safeI I h s.
  Hint Constructors safeI : safe.

  Lemma safeI_sound: forall (I: heap->stmt->Prop) h s,
    (forall h s, I h s -> safe h s) ->
    safeI I h s ->
    safe h s.
  Proof.
    intros.
    revert h s H0.
    cofix; intros.
    inversion H0; subst; clear H0.
    * constructor.
    * constructor.
    destruct H1 as [h'[s'[??]]].
    exists h' s'; split; auto.
    destruct H1; auto.
  Qed.

  Lemma safeI_complete: forall (I: heap->stmt->Prop) h s,
    safe h s ->
    safeI I h s.
  Proof.
    intros.
    revert h s H.
    cofix; intros.
    inversion H; subst; clear H.
    * constructor.
    * constructor.
    destruct H0 as [h'[s'[??]]].
    exists h' s'; split; auto.
  Qed.

  Lemma safeI_bisim: forall (I: heap->stmt->Prop) h s1 s2,
    bisimilar s1 s2 ->
    Proper (eq ==> bisimilar==>iff) I ->
    safeI I h s1 ->
    safeI I h s2.
  Proof.
    cofix; intros.
    inversion H1; subst; clear H1.
    * apply bisim_ret1 in H; subst; auto with safe.
    * destruct H2 as [h'[s'[Hstep Hsafe']]].
    specialize (safe_bisim h').
    constructor.
    edestruct bisim_step1 as [s2'[??]]; eauto.
    exists h' s2'; split; auto.
    intuition eauto.
    symmetry in H3.
    left; eapply H0; eauto.
  Qed.

  Lemma safeI_heap_equiv: forall I h1 h2 s,
    heap_equiv h1 h2 ->
    Proper (heap_equiv ==> eq ==> iff) I ->
    safeI I h1 s ->
    safeI I h2 s.
  Proof.
    cofix; intros.
    inversion H1; subst; clear H1.
    * constructor.
    * destruct H2 as [h'[s'[Hstep Hsafe']]].
    specialize (safe_heap_equiv h').
    edestruct step_heap_equiv1 as [h2'[??]]; eauto.
    constructor; eauto.
    exists h2' s'; split; auto.
    intuition eauto.
    symmetry in H2.
    left; eapply H0; eauto.
  Qed.

  Add Parametric Morphism I (H: Proper (heap_equiv ==> bisimilar ==> iff) I): (safeI I)
    with signature equiv ==> bisimilar ==> iff
    as safeI_m.
  Proof.
    split; intros;
      [ | symmetry in H0, H1];
      eapply safeI_bisim, safeI_heap_equiv; eauto;
      simpl_relation; eapply H; eauto; reflexivity.
  Qed.

  Lemma safeI_weaken: forall (I1 I2: heap->stmt->Prop) h s,
    safeI I1 h s ->
    (forall h s, I1 h s -> I2 h s \/ safeI I2 h s) ->
    safeI I2 h s.
  Proof.
    intros I1 I2 h s Hsafe1 HI.
    revert h s Hsafe1.
    cofix; intros.
    inversion Hsafe1; subst; clear Hsafe1.
    * constructor.
    * constructor.
    destruct H as [h'[s'[??]]].
    exists h' s'; split; auto.
    destruct H0; auto.
  Qed.

  Lemma safeI_bind_ret: forall I h v k,
    safeI I h (k v) ->
    safeI I h (x <- ret v; k x).
  Proof.
    constructor.
    exists h (k v); split; auto.
    apply s_bind_ret.
  Qed.
  Hint Resolve safeI_bind_ret : safe.

  Lemma safeI_bind_ret': forall (I: heap->stmt->Prop) h v k,
    I h (k v) ->
    safeI I h (x <- ret v; k x).
  Proof.
    constructor.
    exists h (k v); split; auto.
    apply s_bind_ret.
  Qed.
  Hint Resolve safeI_bind_ret' : safe.

  Lemma safeI_read: forall I h a v k,
    safeI I h (k v) ->
    h a = Some v ->
    safeI I h (x <- read a; k x).
  Proof.
    constructor.
    exists h (ret v >>= k); split;
      auto with safe.
  Qed.
  Hint Resolve safeI_read : safe.

  Lemma safeI_read': forall (I: heap->stmt->Prop) h a v k,
    I h (k v) ->
    h a = Some v ->
    safeI I h (x <- read a; k x).
  Proof.
    constructor.
    exists h (ret v >>= k); split;
      auto with safe.
  Qed.
  Hint Resolve safeI_read' : safe.

  Lemma safeI_write: forall I h a v v0 k,
    safeI I (upd_heap h a v) (ret 1 >>= k) ->
    h a = Some v0 ->
    safeI I h (write a v >>= k).
  Proof.
    constructor.
    exists (upd_heap h a v) (ret 1 >>= k); split;
      eauto with safe.
  Qed.
  Hint Resolve safeI_write : safe.

  Lemma safeI_write': forall (I: heap->stmt->Prop) h a v v0 k,
    I (upd_heap h a v) (ret 1 >>= k) ->
    h a = Some v0 ->
    safeI I h (write a v >>= k).
  Proof.
    constructor.
    exists (upd_heap h a v) (ret 1 >>= k); split;
      eauto with safe.
  Qed.
  Hint Resolve safeI_write' : safe.

  Lemma safeI_step: forall I h s h' s',
    safeI I h s ->
    step h s h' s' ->
    I h' s' \/ safeI I h' s'.
  Proof.
    intros.
    inversion H; subst.
    * inversion H0.
    * destruct H1 as [h''[s''[? Hsafe']]].
    edestruct step_deterministic
      with (h1':=h'') (h2':=h') as [??];
      eauto; subst h'' s''.
    assumption.
  Qed.
  Hint Resolve safeI_step : safe.

  Lemma safeI_bind_step: forall I h s k h' s',
    step h s h' s' ->
    safeI I h' (s' >>= k) ->
    safeI I h (s >>= k).
  Proof.
    constructor.
    exists h' (s' >>= k); split; auto with safe.
  Qed.
  Hint Resolve safeI_bind_step : safe.

  Lemma safeI_bind_step': forall (I: heap->stmt->Prop) h s k h' s',
    step h s h' s' ->
    I h' (s' >>= k) ->
    safeI I h (s >>= k).
  Proof.
    constructor.
    exists h' (s' >>= k); split; auto with safe.
  Qed.
  Hint Resolve safeI_bind_step' : safe.


