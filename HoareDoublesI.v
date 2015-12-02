Require Import Coq.Program.Syntax.
Require Export ZArith.
Require Import Coq.Program.Basics.
Require Import SetoidTactics.
Require Import SetoidClass.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.

Require Import HDI.Util.
Require Import HDI.CoInduction.
Require Import HDI.Syntax.
Require Import HDI.Heap.
Require Import HDI.OpSem.
Require Import HDI.Bisimulation.
Require Import HDI.SafetyI.
Require Export HDI.Predicates.

Local Open Scope Z.
Local Open Scope stmt.

  Definition in_inv (I: predicate heap->stmt->Prop) x s :=
    exists y s', x |-- y /\ bisimilar s s' /\ I y s'.

  Definition incl_inv (I1 I2: predicate heap->stmt->Prop) :=
    forall x s, I1 x s -> I2 x s.

  Definition inv_union (I1 I2: predicate heap -> stmt -> Prop) : predicate heap -> stmt -> Prop :=
    fun x s => I1 x s \/ I2 x s.

  Lemma incl_inv_in: forall I1 I2 x s,
    incl_inv I1 I2 ->
    in_inv I1 x s ->
    in_inv I2 x s.
  Proof. firstorder. Qed.
  Global Hint Resolve incl_inv_in : safe.

  Lemma in_inv_eq: forall (I: predicate heap->stmt->Prop) x s,
    I x s ->
    in_inv I x s.
  Proof. firstorder. Qed.
  Global Hint Resolve in_inv_eq : safe.

  Lemma incl_inv_refl: forall I,
    incl_inv I I.
  Proof. firstorder. Qed.
  Global Hint Immediate incl_inv_refl : safe.

  Lemma in_inv_entails: forall (I: predicate heap->stmt->Prop) x y s,
    in_inv I y s ->
    x |-- y ->
    in_inv I x s.
  Proof. firstorder. Qed.
  Global Hint Resolve in_inv_entails : safe.

  Lemma in_inv_bisim: forall (I: predicate heap->stmt->Prop) x s1 s2,
    in_inv I x s2 ->
    bisimilar s1 s2 ->
    in_inv I x s1.
  Proof.
    unfold in_inv; intuition auto.
    setoid_rewrite H0.
    auto.
  Qed.
  Global Hint Resolve in_inv_bisim : safe.

  Lemma incl_inv_union1: forall I1 I2,
    incl_inv I1 (inv_union I1 I2).
  Proof. firstorder. Qed.

  Lemma incl_inv_union2: forall I1 I2,
    incl_inv I2 (inv_union I1 I2).
  Proof. firstorder. Qed.
  Hint Resolve incl_inv_union1 incl_inv_union2 : safe.

  Lemma in_inv_forall: forall B (b:B) I x s,
    in_inv I (x b) s ->
    in_inv I (All_ b:B, x b) s.
  Proof. firstorder. Qed.
  Global Hint Resolve in_inv_forall : safe.

  Lemma in_inv_exists: forall I h x s,
    in_inv I x s ->
    h |= x ->
    exists y s', h|=y /\ bisimilar s s' /\ I y s'.
  Proof. firstorder. Qed.
  Global Hint Resolve in_inv_exists : safe.

  Add Parametric Morphism : in_inv
    with signature eq ==> equiv ==> bisimilar ==> iff
    as in_inv_m.
  Proof.
    split; intros; [ symmetry in H0 | symmetry in H];
      (eapply in_inv_entails;
        [ eapply in_inv_bisim | rewrite <-H; reflexivity ];
        eauto).
  Qed.

  Add Parametric Morphism : in_inv
    with signature incl_inv ++> entails --> eq ==> impl
    as in_inv_d.
  Proof. firstorder. Qed.

  Add Parametric Morphism : inv_union
    with signature incl_inv ++> incl_inv ++> incl_inv
    as inv_union_d.
  Proof. firstorder. Qed.

  Global Instance incl_inv_preorder : PreOrder incl_inv.
  Proof. firstorder. Qed.

  Lemma in_inv_union: forall I1 I2 x s,
    in_inv (inv_union I1 I2) x s ->
    in_inv I1 x s \/ in_inv I2 x s.
  Proof. firstorder. Qed.

  Lemma or_dup: forall P,
    (P \/ P) <-> P.
  Proof. intuition idtac. Qed.

  Lemma incl_inv_union_dup: forall I,
    incl_inv (inv_union I I) I.
  Proof. firstorder. Qed.


  Definition hoare_double (I: predicate heap->stmt->Prop) (x: predicate heap) (s: stmt) :=
    forall h, h |= x ->
      safeI (fun h s => exists y s', h |= y /\ bisimilar s s' /\ I y s') h s.

  Definition hoare_double_gen (I1 I2: predicate heap->stmt->Prop) :=
    forall (x: predicate heap) (s: stmt),
      I1 x s ->
      hoare_double I2 x s.

  Definition hoare_double' (I: predicate heap->stmt->Prop) (x: predicate heap) (s: stmt) :=
    in_inv I x s \/ hoare_double I x s.

  Notation "I ||- {{ x }} s" :=
    (hoare_double I x%pred s%stmt)
    (no associativity, at level 65, s at level 42).

  Notation "I ||= {{ x }} s" :=
    (hoare_double' I x%pred s%stmt)
    (no associativity, at level 65, s at level 42).

  Lemma hd_bisim: forall I x s1 s2,
    bisimilar s1 s2 ->
    I ||- {{x}}  s1 ->
    I ||- {{x}}  s2.
  Proof.
    unfold hoare_double, incl_inv.
    intuition auto.
    eapply safeI_bisim; eauto.
    simpl_relation.
    setoid_rewrite H3 at 1.
    reflexivity.
  Qed.

  Lemma hd'_bisim: forall I x s1 s2,
    bisimilar s1 s2 ->
    I ||= {{x}}  s1 ->
    I ||= {{x}}  s2.
  Proof.
    unfold hoare_double'.
    intuition eauto using hd_bisim.
    left; rewrite <-H; auto.
  Qed.

  Lemma hd_weaken: forall I1 I2 x y s,
    I1 ||- {{y}}  s ->
    x |-- y ->
    incl_inv I1 I2 ->
    I2 ||- {{x}}  s.
  Proof.
    unfold hoare_double, incl_inv.
    intuition auto.
    eapply safeI_weaken; intros; eauto.
    destruct H3 as [z[s1[?[??]]]]; eauto 8.
  Qed.

  Lemma hd_weaken': forall I x y s,
    I ||- {{y}}  s ->
    x |-- y ->
    I ||- {{x}}  s.
  Proof.
    intros; eapply hd_weaken; eauto; reflexivity.
  Qed.

  Lemma hd'_weaken: forall I1 I2 x y s,
    I1 ||= {{y}}  s ->
    x |-- y ->
    incl_inv I1 I2 ->
    I2 ||= {{x}}  s.
  Proof.
    unfold hoare_double'.
    intuition eauto using hd_weaken.
    left; firstorder.
  Qed.

  Lemma hd'_weaken': forall I x y s,
    I ||= {{y}}  s ->
    x |-- y ->
    I ||= {{x}}  s.
  Proof.
    intros; eapply hd'_weaken; eauto; reflexivity.
  Qed.

  Add Parametric Morphism : hoare_double
    with signature eq ==> equiv ==> bisimilar ==> iff
    as hoare_double_m.
  Proof.
    split; intros;
      eapply hd_bisim, hd_weaken;
      eauto;
      try solve
      [ apply equiv_sub_entails; eauto with pred
      | reflexivity
      | symmetry; assumption
      ].
  Qed.

  Add Parametric Morphism : hoare_double'
    with signature eq ==> equiv ==> bisimilar ==> iff
    as hoare_double'_m.
  Proof.
    split; intros;
      eapply hd'_bisim, hd'_weaken;
      eauto;
      try solve
      [ apply equiv_sub_entails; eauto with pred
      | reflexivity
      | symmetry; assumption
      ].
  Qed.

  Add Parametric Morphism : hoare_double
    with signature incl_inv ++> entails --> eq ==> impl
    as hoare_double_d.
  Proof.
    unfold impl; eauto using hd_weaken.
  Qed.

  Add Parametric Morphism : hoare_double'
    with signature incl_inv ++> entails --> eq ==> impl
    as hoare_double'_d.
  Proof.
    unfold impl; eauto using hd'_weaken.
  Qed.

  Lemma hd_exists: forall A I x s,
    (forall a:A, I ||-{{x a}}  s) ->
    I ||-{{Ex_ a:A, x a}}  s.
  Proof. firstorder. Qed.
  Global Hint Resolve hd_exists : safe.

  Lemma hd_forall: forall A (a:A) I x s,
    I ||-{{x a}}  s ->
    I ||-{{All_ a:A, x a}}  s.
  Proof. firstorder. Qed.
  Global Hint Resolve hd_forall : safe.

  Lemma hd'_inv: forall I x s,
    in_inv I x s ->
    I ||= {{x}}  s.
  Proof. left; auto. Qed.
  Global Hint Resolve hd'_inv : safe.

  Lemma hd'_safe: forall I x s,
    I ||- {{x}}  s ->
    I ||= {{x}}  s.
  Proof. right; auto. Qed.
  Global Hint Resolve hd'_safe : safe.

  Lemma hd'_forall: forall A (a:A) I x s,
    I ||={{x a}}  s ->
    I ||={{All_ a:A, x a}}  s.
  Proof. firstorder. Qed.
  Global Hint Resolve hd'_forall : safe.

  Lemma hd_coind: forall (I I': predicate heap -> stmt -> Prop) x s,
    (forall x s,
      I' x s ->
      inv_union I I' ||- {{x}}  s) ->
    in_inv I' x s ->
    I ||- {{x}}  s.
  Proof.
    intros ? ? ? ? Hsafe_ Hin.
    assert (Hsafe: forall x s, in_inv I' x s -> inv_union I I' ||- {{x}}  s).
    { intros.
      destruct H as [y[s1[Hy[Hbisim ?]]]].
      rewrite Hy, Hbisim; eauto.
    }
    clear Hsafe_.
    unfold hoare_double.
    intros h Hx.
    cut (in_inv I' x s
        \/ safeI (fun h' s' => exists y s'', h'|=y /\ bisimilar s' s'' /\ (inv_union I I') y s'') h s);
      [ | solve[auto with safe] ].
    clear Hin.
    revert h x s Hx.
    cofix; intros.
    destruct H as [Hin|Hsafe2].
    * specialize (Hsafe x s Hin h Hx).
    inversion Hsafe; subst; clear Hsafe.
    - constructor.
    - constructor.
    destruct H as [h'[s'[Hstep Hsafe']]].
    specialize (hd_coind h' (just h')).
    exists h' s'; split; auto.
    destruct Hsafe' as [ [z[s0[Hz[Hbisim [Hin'|Hin']]]]] | Hsafe'];
      eauto 7;
      solve [right; eapply hd_coind; eauto 7 with safe pred].
    * inversion Hsafe2; subst; clear Hsafe2.
    - constructor.
    - constructor.
    destruct H as [h'[s'[Hstep Hsafe']]].
    specialize (hd_coind h' (just h')).
    exists h' s'; split; auto.
    destruct Hsafe' as [ [z[s0[Hz[Hbisim [Hin'|Hin']]]]] | Hsafe'];
      eauto 7;
      solve [right; eapply hd_coind; eauto 7 with safe pred].
  Qed.

  Lemma hd'_coind: forall (I I': predicate heap -> stmt -> Prop) x s,
    (forall x s,
      I' x s ->
      inv_union I I' ||- {{x}}  s) ->
    in_inv I' x s ->
    I ||= {{x}}  s.
  Proof.
    eauto using hd_coind with safe.
  Qed.

  Lemma hd_coindI: forall (I I': predicate heap -> stmt -> Prop) x s,
    (forall I'' x s,
      I' x s ->
      incl_inv I I'' ->
      incl_inv I' I'' ->
      I'' ||- {{x}}  s) ->
    in_inv I' x s ->
    I ||- {{x}}  s.
  Proof.
    eauto using hd_coind with safe.
  Qed.

  Lemma hd'_coindI: forall (I I': predicate heap -> stmt -> Prop) x s,
    (forall I'' x s,
      I' x s ->
      incl_inv I I'' ->
      incl_inv I' I'' ->
      I'' ||- {{x}}  s) ->
    in_inv I' x s ->
    I ||= {{x}}  s.
  Proof.
    eauto using hd_coind with safe.
  Qed.

  Lemma in_inv_hoare_double: forall I x s,
    in_inv (hoare_double I) x s <-> hoare_double I x s.
  Proof.
    split; [ intros [y[s'[H1[H2 ?]]]] | intros ].
    rewrite H1, H2; assumption.
    exists x s; split; try split; try reflexivity; auto.
  Qed.

  Lemma in_inv_hoare_double': forall I x s,
    in_inv (hoare_double' I) x s <-> hoare_double' I x s.
  Proof.
    split; [ intros [y[s'[H1[H2 ?]]]] | intros ].
    rewrite H1, H2; assumption.
    exists x s; split; try split; try reflexivity; auto.
  Qed.

  Lemma hoare_double_coind_principle: forall (I1 I2: predicate heap -> stmt -> Prop) x s,
    I2 x s ->
    hoare_double_gen I2 (inv_union I1 I2) ->
    hoare_double I1 x s.
  Proof.
    intros I1 I2 x s HI2 Hsafe.
    eapply hd_coindI;
      [ clear x s HI2; intros I'' x s HI2 Hincl1 Hincl2
      | apply in_inv_eq; eauto ].
    apply Hsafe in HI2; clear Hsafe.
    hnf; intros.
    eapply safeI_weaken; eauto.
    simpl; intros.
    destruct H0 as [y[s'[Hy[Hbisim Hsafe']]]].
    destruct Hsafe' as [Hsafe'|Hsafe'];
      eauto 7 with safe.
  Qed.

  Lemma hoare_double_gen_hd_intro: forall (I1 I2: predicate heap -> stmt -> Prop),
    (forall I3: _ -> _ -> Prop,
      (forall x s,
        I1 x s ->
        hoare_double' I3 x s) ->
      incl_inv I2 I3 ->
      hoare_double_gen I1 I3) ->
    hoare_double_gen I1 (inv_union I2 I1).
  Proof.
    unfold hoare_double_gen; intuition auto.
    eapply H; intros; eauto;
    intuition eauto with safe.
  Qed.

  Lemma hoare_double_coind: forall (I1 I2: predicate heap -> stmt -> Prop),
    (forall I3: _ -> _ -> Prop,
      (forall x s, I2 x s -> hoare_double' I3 x s) ->
(*      (forall x s, I1 x s -> hoare_double' I3 x s) ->*)
      incl_inv I1 I3 ->
      hoare_double_gen I2 I3) ->
    forall x s,
    I2 x s ->
    hoare_double I1 x s.
  Proof.
    intros.
    apply (hoare_double_coind_principle I1 I2 x s); auto.
    apply hoare_double_gen_hd_intro.
    intros; eauto.
  Qed.

  Global Instance coind_hoare_double {I} `{co_rel:CoRelation _}  {x s}
    : CoIndRelation (hoare_double I x s) | 100 :=
    {| coind_rel:= coind_co_rel (x,s) |}.

  Global Program Instance hoare_double_cind (I1 I2: predicate heap -> stmt -> Prop) x s
    : CoIndPrinciple I2 (hoare_double I1 x s) :=
    {| coind_principle := fun H1 H2 =>
        hoare_double_coind I1 I2 H2 x s H1
    |}.

  Ltac hd_coind_ :=
    let G:= thegoal in
    (* rephrase in a friendler way: provide helper lemmas to solve gen relations *)
    coind_ ltac:(fun names =>
      (**)
      try match thegoal with
      | hoare_double_gen ?I1 ?I2 =>
        try intro_relation_with_names names
      | _ =>
        try intro_relation_with_names names
      end).

  Tactic Notation "hd_coind" :=
    hd_coind_.


  Lemma ret_ok: forall I v F,
    I ||-{{F}}  ret v.
  Proof.
    unfold hoare_double; intros.
    eauto with safe.
  Qed.

  Lemma ret_bind_ok: forall I v F k,
    I ||={{F}}  k v ->
    I ||-{{F}}  x <- ret v; k x.
  Proof.
    unfold hoare_double; intros.
    destruct H; eauto with safe.
  Qed.

  Hint Resolve ret_ok ret_bind_ok : safe.

  Lemma read_ok: forall I a v F k,
    I ||= {{a |-> v && F}}  k v ->
    I ||- {{a |-> v && F}}  x <- read a; k x.
  Proof.
    unfold hoare_double; intros.
    destruct H; eauto with safe pred.
  Qed.

  Lemma read_str0_0_ok: forall I a v F k,
    I ||= {{a |->0 v && F}}  k (match v with String c _ => Z_of_ascii c | _ => 0 end) ->
    I ||- {{a |->0 v && F}}  x <- read a; k x.
  Proof.
    unfold getd; intros.
    destruct v; simpl in *.
    * rewrite str0_empty in *.
    apply read_ok; auto.
    * rewrite str0_cons in *.
    rewrite <-inter_assoc in H |- *.
    apply read_ok; auto.
  Qed.

  Lemma write_ok: forall I a v v0 F k,
    pred_free F a ->
    I ||= {{a |-> v && F}}  k 1 ->
    I ||- {{a |-> v0 && F}}  write a v >>= k.
  Proof.
    unfold hoare_double; intros.
    eapply safeI_write; eauto with safe pred.
    destruct H0; eauto with safe pred.
    - eapply safeI_bind_ret'; eauto with safe pred.
    apply in_inv_exists with (x:=(a|->v && F)%pred); auto.
    firstorder.
    - eapply safeI_bind_ret; eauto with safe pred.
    firstorder.
  Qed.


  Ltac step :=
    match goal with
    | |- _ ||= {{_}} _ => apply hd'_safe; step
    | |- ?I ||- {{?x}} ?s =>
      match s with
      | ret _ => apply ret_ok
      | bind (ret _) _ => apply ret_bind_ok
      | _ <- act (read ?a); _ =>
        match x with
        | appcontext[pts a ?v'] =>
          eapply hd_weaken'; [apply read_ok with (v:=v') | try reflexivity]
        | appcontext[str0 a ?v'] =>
          eapply hd_weaken'; [apply read_str0_0_ok with (v:=v') | try reflexivity]
        | _ =>
          eapply hd_weaken'; [apply read_ok | try reflexivity]
        end
      | _ <- act (write _); _ => eapply hd_weaken'; [apply write_ok | try reflexivity]
      | bind (bind _ _) _ => rewrite !bisim_bind_assoc; step
      end
    end.
