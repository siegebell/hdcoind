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

  (* We only need simple algebriac properties, like associativity of bind,
    so a simple and overly strong definition will do. *)
  Definition simulation (R: relation stmt) :=
    forall s1 s2, R s1 s2 ->
    (forall h h' s1',
      step h s1 h' s1' ->
      exists s2',
        step h s2 h' s2' /\ R s1' s2') /\
    (forall v,
      s1 = ret v -> s2 = ret v).

  Definition bisimilar s1 s2:= exists (R: relation stmt), R s1 s2 /\ simulation R /\ simulation (flip R).

  Lemma bisim_step1: forall s1 s2 h h' s1',
    bisimilar s1 s2 ->
    step h s1 h' s1' ->
    exists s2',
      step h s2 h' s2' /\ bisimilar s1' s2'.
  Proof.
    unfold bisimilar, flip, simulation; intros.
    destruct H as [R[HR[Hsim1 Hsim2]]].
    edestruct Hsim1 as [Hsim1' _]; eauto.
    edestruct Hsim1' as [s2'[??]]; eauto 8.
  Qed.

  Lemma bisim_ret1: forall v s,
    bisimilar (ret v) s -> s = ret v.
  Proof.
    unfold bisimilar, flip, simulation; intros.
    destruct H as [R[HR[Hsim1 Hsim2]]].
    edestruct Hsim1 as [_ Hret1]; eauto.
  Qed.

  Lemma bisim_step2: forall s1 s2 h h' s2',
    bisimilar s1 s2 ->
    step h s2 h' s2' ->
    exists s1',
      step h s1 h' s1' /\ bisimilar s1' s2'.
  Proof.
    unfold bisimilar, flip, simulation; intros.
    destruct H as [R[HR[Hsim1 Hsim2]]].
    edestruct Hsim2 as [Hsim2' _]; eauto.
    edestruct Hsim2' as [s1'[??]]; eauto 8.
  Qed.

  Lemma bisim_ret2: forall v s,
    bisimilar s (ret v) -> s = ret v.
  Proof.
    unfold bisimilar, flip, simulation; intros.
    destruct H as [R[HR[Hsim1 Hsim2]]].
    edestruct Hsim2 as [_ Hret]; eauto.
  Qed.

  Global Instance bisim_equiv: Equivalence bisimilar.
  Proof.
    constructor; hnf; intros.
    * eexists eq; split; auto; split;
      hnf; unfold flip; intros; subst; eauto.
    * eexists (fun s1 s2 => bisimilar s2 s1);
      split; auto.
    clear x y H; split;
      hnf; simpl; intros;
      intuition (subst; eauto using bisim_step1, bisim_step2, bisim_ret1, bisim_ret2).
    * eexists (fun s1 s3 => exists s2, bisimilar s1 s2 /\ bisimilar s2 s3);
      split; eauto.
    unfold flip.
    clear x y z H H0; split;
      hnf; simpl;
      intros x z [y[H1 H2]]; split; intros.
    - edestruct bisim_step1 with (s1:=x) as [y'[??]]; eauto.
    edestruct bisim_step1 with (s1:=y) as [z'[??]]; eauto.
    - subst.
    eapply bisim_ret1 in H1; subst.
    eapply bisim_ret1 in H2; subst.
    reflexivity.
    - edestruct bisim_step2 with (s1:=y) as [y'[??]]; eauto.
    edestruct bisim_step2 with (s1:=z) as [z'[??]]; eauto.
    - subst.
    eapply bisim_ret2 in H2; subst.
    eapply bisim_ret2 in H1; subst.
    reflexivity.
  Qed.

  Lemma bisim_bind_assoc: forall s1 k2 k3,
    bisimilar ((s1 >>= k2) >>= k3) (x<-s1; (k2 x >>= k3)).
  Proof.
    intros.
    exists (fun p q =>
      (exists s1 k2 k3, p = (s1 >>= k2) >>= k3 /\ q = x<-s1; (k2 x >>= k3)) \/ p=q)%stmt.
    split; eauto 8.
    clear s1 k2 k3.
    unfold flip.
    split; intros p q [ [s1[k2[k3[??]]]] | ? ]; subst;
      split; intros; eauto; try discriminate.
    * inversion H; subst; clear H.
    inversion H4; subst; clear H4.
    - eexists; split.
    apply s_bind1; eauto.
    eauto 8.
    - eexists; split; eauto with safe.
    * inversion H; subst; clear H;
      eexists; split; eauto 8 with safe.
  Qed.

