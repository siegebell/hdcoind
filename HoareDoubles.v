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
Require Export HDI.Predicates.

Local Open Scope Z.
Local Open Scope stmt.


  Definition hoare_double (x: predicate heap) (s: stmt) :=
    forall h, h |= x -> safe h s.

  Notation "|-{{ x }} s" :=
    (hoare_double x%pred s%stmt)
    (no associativity, at level 65, s at level 42).

  Lemma hd_weaken: forall x y s,
    |-{{y}}  s ->
    x |-- y ->
    |-{{x}}  s.
  Proof.
    unfold hoare_double.
    intuition auto.
  Qed.

  Add Parametric Morphism : hoare_double
    with signature entails --> eq ==> impl
    as hd_d.
  Proof. firstorder. Qed.

  Lemma hd_exists: forall A x s,
    (forall a:A, |-{{x a}}  s) ->
    |-{{Ex_ a:A, x a}}  s.
  Proof. firstorder. Qed.

  Lemma hd_forall: forall A (a:A) x s,
    |-{{x a}}  s ->
    |-{{All_ a:A, x a}}  s.
  Proof. firstorder. Qed.


  Lemma ret_ok: forall v F k,
    |-{{F}}  k v ->
    |-{{F}}  x <- ret v; k x.
  Proof.
    unfold hoare_double; auto with safe.
  Qed.

  Lemma read_ok: forall a v F k,
    |-{{a |-> v && F}}  k v ->
    |-{{a |-> v && F}}  x <- read a; k x.
  Proof.
    unfold hoare_double; eauto with safe pred.
  Qed.

  Definition pred_free (x: predicate heap) (a:Z) :=
    forall h v, h |= x -> upd_heap h a v |= x.

  Lemma write_ok: forall a v v0 F k,
    pred_free F a ->
    |-{{a |-> v && F}}  k 1 ->
    |-{{a |-> v0 && F}}  write a v >>= k.
  Proof.
    unfold hoare_double; eauto with safe pred.
    intros.
    eapply safe_write;
      [ firstorder | eauto with pred ].
  Qed.

