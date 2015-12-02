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

Local Open Scope stmt.

CoInductive safe (h: heap) : stmt -> Prop :=
  | safe_ret: forall v,
    safe h (ret v)
  | safe_exists_step: forall s,
    (exists h' s',
      step h s h' s' /\ safe h' s') ->
    safe h s.
Hint Constructors safe : safe.



  Lemma safe_bisim: forall h s1 s2,
    bisimilar s1 s2 ->
    safe h s1 ->
    safe h s2.
  Proof.
    cofix; intros.
    inversion H0; subst; clear H0.
    * apply bisim_ret1 in H; subst; auto with safe.
    * destruct H1 as [h'[s'[Hstep Hsafe']]].
    specialize (safe_bisim h').
    constructor.
    edestruct bisim_step1 as [s2'[??]]; eauto.
  Qed.

  Lemma safe_heap_equiv: forall h1 h2 s,
    heap_equiv h1 h2 ->
    safe h1 s ->
    safe h2 s.
  Proof.
    cofix; intros.
    inversion H0; subst; clear H0.
    * constructor.
    * destruct H1 as [h'[s'[Hstep Hsafe']]].
    specialize (safe_heap_equiv h').
    edestruct step_heap_equiv1 as [h2'[??]]; eauto.
    constructor; eauto.
  Qed.

  Add Parametric Morphism : safe
    with signature equiv ==> bisimilar ==> iff
    as safe_m.
  Proof.
    split; intros;
      [ | symmetry in H, H0];
      eauto using safe_bisim, safe_heap_equiv.
  Qed.

  Lemma safe_bind_ret: forall h v k,
    safe h (k v) ->
    safe h (x <- ret v; k x).
  Proof.
    constructor.
    exists h (k v); split; auto.
    apply s_bind_ret.
  Qed.
  Hint Resolve safe_bind_ret : safe.

  Lemma safe_read: forall h a v k,
    safe h (k v) ->
    h a = Some v ->
    safe h (x <- read a; k x).
  Proof.
    constructor.
    exists h (ret v >>= k); split;
      auto with safe.
  Qed.
  Hint Resolve safe_read : safe.

  Lemma safe_write: forall h a v v0 k,
    safe (upd_heap h a v) (ret 1 >>= k) ->
    h a = Some v0 ->
    safe h (write a v >>= k).
  Proof.
    constructor.
    exists (upd_heap h a v) (ret 1 >>= k); split;
      eauto with safe.
  Qed.
  Hint Resolve safe_write : safe.

  Lemma safe_step: forall h s h' s',
    safe h s ->
    step h s h' s' ->
    safe h' s'.
  Proof.
    intros.
    inversion H; subst.
    * inversion H0.
    * destruct H1 as [h''[s''[??]]].
    edestruct step_deterministic
      with (h1':=h'') (h2':=h') as [??];
      eauto; subst h'' s''.
    assumption.
  Qed.
  Hint Resolve safe_step : safe.

  Lemma safe_bind_step: forall h s k h' s',
    step h s h' s' ->
    safe h' (s' >>= k) ->
    safe h (s >>= k).
  Proof.
    constructor.
    exists h' (s' >>= k); split; auto with safe.
  Qed.
  Hint Resolve safe_bind_step : safe.

  Lemma unsafe_abort: forall h,
    safe h abort ->
    False.
  Proof.
    intros.
    inversion H; subst.
    destruct H0 as [?[?[Hstep ?]]].
    inversion Hstep.
  Qed.
  Hint Resolve unsafe_abort : safe.
  
