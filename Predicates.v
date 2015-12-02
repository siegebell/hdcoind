Require Import Coq.Program.Syntax.
Require Export ZArith.
Require Import Coq.Program.Basics.
Require Import SetoidTactics.
Require Import SetoidClass.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.


Require Import HDI.Util.
Require Import HDI.Heap.

Delimit Scope pred with pred.

  Record predicate (A:Type) {sa: Setoid A} : Type :=
  { pred_fun: A -> Prop
  ; pred_fun_equiv: forall x y, x == y -> pred_fun x -> pred_fun y
  }.
  Bind Scope pred with predicate.
  Arguments pred_fun {_ _} _%pred _.

  Hint Resolve @pred_fun_equiv : pred.

  Notation "a |= x" := (pred_fun x%pred a) (at level 80, x at next level, no associativity).

Section PredEquiv.
  Context {A:Type} {sa: Setoid A}.

  Definition pred_equiv (x y: predicate A) := forall a, a|=x <-> a|=y.
  Infix "==" := pred_equiv.

  Global Instance pred_equiv_eq: Equivalence pred_equiv.
  Proof. firstorder. Qed.

  Global Instance pred_setoid: Setoid (predicate A) := {| equiv:=pred_equiv |}.

End PredEquiv.


  Lemma pred_equiv_models: forall A (sa:Setoid A) (x: @predicate A sa) (y: @predicate A sa),
    pred_equiv x y ->
    forall a,
    a |= x ->
    a |= y.
  Proof. intros ? ? ? ? Heq ? Hm; apply Heq, Hm. Qed.

  Definition entails {A} {sa:Setoid A} (x y: predicate A):=
    forall a, a|=x -> a|=y.
  Notation "x '|--' y" := (entails x%pred y%pred) (at level 80, y at next level, no associativity).

  Global Instance entails_preorder A sa: PreOrder (@entails A sa).
  Proof. firstorder. Qed.

  Definition pred_free (x: predicate heap) (a:Z) :=
    forall h v, h |= x -> upd_heap h a v |= x.

  Add Parametric Morphism A sa: (@pred_fun A sa)
    with signature equiv ==> equiv ==> iff
    as pred_fun_m.
  Proof.
    split; intros.
    eapply pred_fun_equiv, pred_equiv_models with (x:=x); eauto.
    eapply pred_fun_equiv, pred_equiv_models with (x:=y); eauto using symmetry.
    symmetry; auto.
  Qed.

  Add Parametric Morphism A sa: (@pred_fun A sa)
    with signature entails ==> eq ==> impl
    as pred_fun_d.
  Proof.
    unfold impl; intros; eauto.
  Qed.

  Section A.
    Context {A:Type} {sa: Setoid A}.

    Obligation Tactic := intuition eauto using @pred_fun_equiv.

    Program Definition top : predicate A:=
      {| pred_fun a:= True |}.
    Fail Next Obligation.

    Program Definition bot : predicate A:=
      {| pred_fun a:= False |}.
    Fail Next Obligation.

    Program Definition just b : predicate A:=
      {| pred_fun a:= a==b |}.
    Next Obligation.
      rewrite <-H; assumption.
    Qed.
    Fail Next Obligation.

    Program Definition inter (x y: predicate A) : predicate A:=
      {| pred_fun a:= a|=x /\ a|=y |}.
    Fail Next Obligation.

    Program Definition union (x y: predicate A) : predicate A:=
      {| pred_fun a:= a|=x \/ a|=y |}.
    Fail Next Obligation.

    Program Definition prop (x: Prop) : predicate A:=
      {| pred_fun a:= x |}.
    Fail Next Obligation.

    Program Definition pex {B} (x: B -> predicate A) : predicate A:=
      {| pred_fun a:= exists b:B, a|=x b |}.
    Next Obligation.
      destruct H0 as [??]; eexists.
      rewrite <-H; eassumption.
    Qed.
    Fail Next Obligation.

    Program Definition pall {B} (x: B -> predicate A) : predicate A:=
      {| pred_fun a:= forall b:B, a|=x b |}.
    Fail Next Obligation.

  End A.

  Section Heap.
    Program Definition pts a v : predicate heap:=
      {| pred_fun h:= h a = Some v |}.
    Fail Next Obligation.

    Definition ptr a : predicate heap:= pex (fun v:Z => pts a v).

    Program Definition ptr_values (v:list (Z*Z)) : predicate heap :=
      {| pred_fun h :=  List.Forall (fun ac => h |= pts (fst ac) (snd ac)) v |}.
    Next Obligation.
      induction v.
      constructor.
      inversion H0; clear H0; subst.
      eapply List.Forall_cons; eauto.
      erewrite <-heap_lookup_equiv; eauto.
    Qed.
    Fail Next Obligation.

    Definition pts_array (a:Z) (v: list Z) : predicate heap :=
      ptr_values (array_ptrs a v).

    Definition str (a: Z) (v: string): predicate heap :=
      pts_array a (map Z_of_ascii (list_of_string v)).

    Definition str0 (a: Z) (v: string): predicate heap :=
      pts_array a (map Z_of_ascii (list_of_string v ++ [zero])).

  End Heap.

  Notation "⏉" := (top) (at level 0, no associativity) : pred.
  Notation "⏊ " := (bot) (at level 0, no associativity) : pred.
  Infix "&&" := inter (at level 40, left associativity) : pred.
  Infix "||" := union (at level 50, left associativity) : pred.
  Notation "'!!' x" := (prop x) (at level 25) : pred.
  Notation "'Ex_'  x ':' T ',' P " := (pex (fun x:T => P%pred)) (at level 65, x at level 99) : pred.
  Notation "'All_'  x ':' T  ',' P " := (pall (fun x:T => P%pred)) (at level 65, x at level 99) : pred.
  Notation "'Ex_'  x ',' P " := (pex (fun x => P%pred)) (at level 65, x at level 99) : pred.
  Notation "'All_'  x ',' P " := (pall (fun x => P%pred)) (at level 65, x at level 99) : pred.
  Notation "'∃'  x ':' T ',' P " := (pex (fun x:T => P%pred)) (at level 65, x at level 99) : pred.
  Notation "'∀'  x ':' T  ',' P " := (pall (fun x:T => P%pred)) (at level 65, x at level 99) : pred.
  Notation "'∃'  x ',' P " := (pex (fun x => P%pred)) (at level 65, x at level 99) : pred.
  Notation "'∀'  x ',' P " := (pall (fun x => P%pred)) (at level 65, x at level 99) : pred.
  Notation "a '|->_'" := (ptr a%Z) (at level 20, no associativity) : pred.
  Notation "a '|->0' s" := (str0 a%Z s%string) (at level 20, no associativity): pred.
  Notation "a '|->' s" := (str a%Z s%string) (at level 20, no associativity): pred.
  Notation "a '|->' v" := (pts a%Z v%Z) (at level 20, no associativity): pred.


Section Lemmas.
  Context {A:Type} {sa: Setoid A}.
  Local Open Scope pred.

  Lemma pred_fun_inter_intro: forall a x y,
    a |= x ->
    a |= y ->
    a |= x && y.
  Proof. firstorder. Qed.

  Lemma pred_fun_inter_elim1: forall a x y,
    a |= x && y ->
    a |= x.
  Proof. firstorder. Qed.

  Lemma pred_fun_inter_elim2: forall a x y,
    a |= x && y ->
    a |= y.
  Proof. firstorder. Qed.

  Lemma pred_fun_union_intro1: forall a x y,
    a |= x ->
    a |= x || y.
  Proof. firstorder. Qed.

  Lemma pred_fun_union_intro2: forall a x y,
    a |= y ->
    a |= x || y.
  Proof. firstorder. Qed.

  Lemma pred_fun_union_elim: forall a x y,
    a |= x || y ->
    a |= x \/ a|= y.
  Proof. firstorder. Qed.

  Lemma pred_fun_exists_intro: forall B a (b:B) x,
    a |= x b ->
    a |= Ex_ b:B, x b.
  Proof. firstorder. Qed.

  Lemma pred_fun_exists_elim: forall B a x,
    a |= Ex_ b:B, x b ->
    exists b:B, a |= x b.
  Proof. intuition eauto. Qed.

  Lemma pred_fun_forall_intro: forall B a x,
    (forall b:B, a |= x b) ->
    a |= All_ b:B, x b.
  Proof. intuition eauto. Qed.

  Lemma pred_fun_forall_elim: forall B a (b:B) x,
    a |= All_ b:B, x b ->
    a |= x b.
  Proof. intuition eauto. Qed.

  Lemma pred_fun_just_intro: forall a,
    a |= just a.
  Proof. unfold just; simpl; intros; reflexivity. Qed.

  Lemma pred_fun_just_elim: forall a b,
    a |= just b ->
    a == b.
  Proof. intros; apply H. Qed.

  Lemma entails_inter_intro: forall x y z,
    z |-- x ->
    z |-- y ->
    z |-- x && y.
  Proof. firstorder. Qed.

  Lemma entails_inter_elim1: forall x y z,
    x |-- z ->
    x && y |-- z.
  Proof. firstorder. Qed.

  Lemma entails_inter_elim2: forall x y z,
    y |-- z ->
    x && y |-- z.
  Proof. firstorder. Qed.

  Lemma entails_union_intro1: forall x y z,
    z |-- x ->
    z |-- x || y.
  Proof. firstorder. Qed.

  Lemma entails_union_intro2: forall x y z,
    z |-- y ->
    z |-- x || y.
  Proof. firstorder. Qed.

  Lemma entails_union_elim: forall x y z,
    x |-- z ->
    y |-- z ->
    x || y |-- z.
  Proof. firstorder. Qed.

  Lemma entails_exists_intro: forall B (b:B) x y,
    x |-- y b ->
    x |-- Ex_ b:B, y b.
  Proof. firstorder. Qed.

  Lemma entails_forall_elim: forall B (b:B) x y,
    x b |-- y ->
    All_ b:B, x b |-- y.
  Proof. firstorder. Qed.

  Lemma just_elim: forall a x,
    a |= x ->
    just a |-- x.
  Proof. unfold just, entails; simpl; intros; rewrite H0; assumption. Qed. 

  Lemma inter_elim: forall x,
    x && x == x.
  Proof. firstorder. Qed.

  Lemma inter_elim1: forall x y,
    x && y |-- x.
  Proof. firstorder. Qed.

  Lemma inter_elim2: forall x y,
    x && y |-- y.
  Proof. firstorder. Qed.

  Lemma union_intro1: forall x y,
    x |-- x || y.
  Proof. firstorder. Qed.

  Lemma union_intro2: forall x y,
    y |-- x || y.
  Proof. firstorder. Qed.

  Lemma union_elim: forall x,
    x || x == x.
  Proof. firstorder. Qed.

  Lemma exists_intro: forall B (b:B) x,
    x b |-- Ex_ b:B, x b.
  Proof. firstorder. Qed.

  Lemma exists_elim: forall B x y,
    (forall b:B, x b |-- y) ->
    Ex_ b:B, x b |-- y.
  Proof. firstorder. Qed.

  Lemma forall_intro: forall B x y,
    (forall b:B, x |-- y b) ->
    x |-- All_ b:B, y b.
  Proof. firstorder. Qed.

  Lemma forall_elim: forall B (b:B) x,
    All_ b:B, x b |-- x b.
  Proof. firstorder. Qed.


  Lemma pred_fun_prop_intro: forall a (P:Prop),
    P ->
    a |= !!P.
  Proof. intuition idtac. Qed.

  Lemma pred_fun_prop_elim: forall a (P:Prop),
    a |= !!P ->
    P.
  Proof. intuition idtac. Qed.

  Lemma prop_intro: forall x (P:Prop),
    P ->
    x |-- !!P.
  Proof. firstorder. Qed.

  Lemma prop_elim: forall x (P:Prop),
    (P -> top |-- x) ->
    !!P |-- x.
  Proof. firstorder. Qed.

  Lemma pred_fun_top_intro: forall a,
    a |= top.
  Proof. firstorder. Qed.

  Lemma pred_fun_bot_elim: forall a,
    a |= bot ->
    False.
  Proof. firstorder. Qed.

  Lemma inter_top1: forall x,
    top && x == x.
  Proof. firstorder. Qed.

  Lemma inter_top2: forall x,
    x && top == x.
  Proof. firstorder. Qed.

  Lemma inter_bot1: forall x,
    bot && x == bot.
  Proof. simpl; unfold pred_equiv. firstorder. Qed.

  Lemma inter_bot2: forall x,
    x && bot == bot.
  Proof. firstorder. Qed.

  Lemma inter_assoc: forall x y z,
    x && (y && z) == (x && y) && z.
  Proof. firstorder. Qed.

  Lemma union_assoc: forall x y z,
    x || (y || z) == (x || y) || z.
  Proof. firstorder. Qed.

  Lemma inter_comm: forall x y,
    y && x == x && y.
  Proof. firstorder. Qed.

  Lemma union_comm: forall x y,
    y || x == x || y.
  Proof. firstorder. Qed.

  Lemma inter_exists1: forall B x y,
    (Ex_ b:B, x b) && y == Ex_ b:B, (x b && y).
  Proof. firstorder. Qed.

  Lemma inter_exists2: forall B x y,
    x && (Ex_ b:B, y b) == Ex_ b:B, (x && y b).
  Proof. firstorder. Qed.

  Lemma inter_forall1: forall B x y,
    (All_ b:B, x b) && y |-- All_ b:B, (x b && y).
  Proof. firstorder. Qed.

  Lemma inter_forall2: forall B x y,
    x && (All_ b:B, y b) |-- All_ b:B, (x && y b).
  Proof. firstorder. Qed.

  Lemma inter_forall1': forall B x y,
    inhabited B ->
    (All_ b:B, x b) && y == All_ b:B, (x b && y).
  Proof. firstorder. Qed.

  Lemma inter_forall2': forall B x y,
    inhabited B ->
    x && (All_ b:B, y b) == All_ b:B, (x && y b).
  Proof. firstorder. Qed.

End Lemmas.

Global Hint Immediate @pred_fun_just_intro : pred.
Global Hint Resolve @pred_fun_just_elim @just_elim: pred.
Global Hint Resolve @pred_fun_inter_intro : pred.
Global Hint Resolve @pred_fun_union_intro1 @pred_fun_union_intro2 : pred.
Global Hint Resolve @entails_inter_intro @entails_inter_elim1 @entails_inter_elim2 : pred.
Global Hint Resolve @entails_union_intro1 @entails_union_intro2 @entails_union_elim : pred.
Global Hint Resolve @pred_fun_prop_intro @prop_intro @prop_elim : pred.
Global Hint Resolve @pred_fun_top_intro @pred_fun_bot_elim : pred.
Global Hint Resolve @pred_fun_exists_intro @pred_fun_forall_intro : pred.
Global Hint Resolve @inter_elim1 @inter_elim2 @union_intro1 @union_intro2 @exists_intro : pred.
Hint Rewrite @inter_exists1 @inter_exists2 @inter_forall1 @inter_forall2 : pred.
Hint Rewrite @inter_top1 @inter_top2 @inter_bot1 @inter_bot2 : pred.
Hint Rewrite @inter_elim @union_elim : pred.


  Add Parametric Morphism A sa : (@just A sa)
    with signature equiv ==> equiv
    as just_m.
  Proof. unfold just; split; simpl; intros; rewrite H in *; assumption. Qed.

  Add Parametric Morphism A sa : (@inter A sa)
    with signature entails ==> entails ==> entails
    as inter_d.
  Proof. auto with pred. Qed.

  Add Parametric Morphism A sa : (@inter A sa)
    with signature equiv ==> equiv ==> equiv
    as inter_m.
  Proof. firstorder. Qed.

  Add Parametric Morphism A sa : (@union A sa)
    with signature entails ==> entails ==> entails
    as union_d.
  Proof. auto with pred. Qed.

  Add Parametric Morphism A sa : (@union A sa)
    with signature equiv ==> equiv ==> equiv
    as union_m.
  Proof. firstorder. Qed.

  Global Instance pred_equiv_sub_equiv A sa: subrelation (@pred_equiv A sa) equiv.
  Proof. firstorder. Qed.

  Global Opaque pred_setoid.


  Section HeapLemmas.
    Local Open Scope pred.

    Lemma pts_lookup: forall h a v,
      h |= a |-> v ->
      h a = Some v.
    Proof.
      unfold pts; simpl; intros; auto.
    Qed.

    Lemma pts_lookup1: forall h a v F,
      h |= a |-> v && F ->
      h a = Some v.
    Proof.
      intros.
      destruct H.
      auto using pts_lookup.
    Qed.

    Lemma pts_upd: forall h a v,
      upd_heap h a v |= a |-> v.
    Proof.
      unfold pts; simpl; intros.
      apply upd_heap_lookup.
    Qed.

    Lemma pts_upd1: forall h a v F,
      upd_heap h a v |= F ->
      upd_heap h a v |= a |-> v && F.
    Proof.
      unfold pts; simpl; intros.
      split; auto; apply pts_upd.
    Qed.

    Lemma ptr_values_nil:
      ptr_values [] == top.
    Proof. apply pred_equiv_sub_equiv. split; simpl; intros; auto. Qed.

    Lemma ptr_values_cons: forall a v l,
      ptr_values ((a,v)::l) == a |-> v && ptr_values l.
    Proof.
      intros; apply pred_equiv_sub_equiv.
      split; simpl; intros; auto.
      * inversion H; clear H; subst.
      intuition auto.
      * intuition auto.
    Qed.

    Lemma ptr_values_app: forall l1 l2,
      ptr_values (l1++l2) == ptr_values l1 && ptr_values l2.
    Proof.
      induction l1; simpl; intros.
      rewrite ptr_values_nil, inter_top1.
      reflexivity.
      destruct a.
      rewrite !ptr_values_cons.
      rewrite IHl1.
      apply inter_assoc.
    Qed.

    Lemma pts_array_nil: forall a,
      pts_array a nil == top.
    Proof.
      unfold pts_array; intros.
      rewrite array_ptrs_nil, ptr_values_nil.
      reflexivity.
    Qed.

    Lemma pts_array_cons: forall a v l,
      pts_array a (v::l) == pts a v && pts_array (1+a) l.
    Proof.
      unfold pts_array; intros.
      rewrite array_ptrs_cons, ptr_values_cons.
      reflexivity.
    Qed.

    Lemma pts_array_app: forall a (l1 l2: list Z),
      pts_array a (l1++l2) == pts_array a l1 && pts_array (a+Z.of_nat (length l1)) l2.
    Proof.
      unfold pts_array; intros.
      rewrite array_ptrs_app, ptr_values_app.
      reflexivity.
    Qed.

    Lemma str_empty: forall a,
      str a "" == top.
    Proof.
      unfold str; intros.
      autorewrite with lists.
      rewrite pts_array_nil.
      reflexivity.
    Qed.

    Lemma str_cons: forall a c s,
      str a (String c s) == pts a c && str (1+a) s.
    Proof.
      unfold str; intros.
      rewrite list_of_string_cons.
      simpl (map _ _).
      apply pts_array_cons.
    Qed.

    Lemma str_app: forall a s1 s2,
      str a (append s1 s2) == str a s1 && str (a+Z.of_nat (str_len s1)) s2.
    Proof.
      unfold str; intros.
      autorewrite with lists.
      rewrite pts_array_app.
      autorewrite with lists.
      reflexivity.
    Qed.

    Lemma str0_str: forall a s,
      str0 a s == str a s && (a+Z.of_nat (str_len s)) |-> zero.
    Proof.
      intros.
      unfold str0, str.
      autorewrite with lists.
      rewrite pts_array_app, pts_array_cons, pts_array_nil.
      autorewrite with lists pred.
      reflexivity.
    Qed.

    Lemma str0_empty: forall a,
      str0 a "" == pts a zero.
    Proof.
      intros.
      rewrite str0_str, str_empty.
      autorewrite with lists pred.
      reflexivity.
    Qed.

    Lemma str0_cons: forall a c s,
      str0 a (String c s) == pts a c && str0 (1+a) s.
    Proof.
      intros.
      rewrite !str0_str, str_cons, inter_assoc.
      autorewrite with lists pred.
      reflexivity.
    Qed.

    Lemma str0_app: forall a s1 s2,
      str0 a (append s1 s2) == str a s1 && str0 (a+Z.of_nat (str_len s1)) s2.
    Proof.
      intros.
      rewrite !str0_str, str_app, inter_assoc.
      autorewrite with lists pred.
      rewrite Z.add_assoc.
      reflexivity.
    Qed.

  End HeapLemmas.

  Global Hint Resolve @pts_lookup @pts_lookup1 @pts_upd @pts_upd1 : pred.
  Hint Rewrite ptr_values_nil pts_array_nil str_empty str0_empty : lists.
  Hint Rewrite ptr_values_cons pts_array_cons str_cons str0_cons : lists.
  Hint Rewrite ptr_values_app pts_array_app str_app str0_app : lists.

Global Instance equiv_sub_entails A sa: subrelation equiv (@entails A sa).
Proof. firstorder. Qed.



