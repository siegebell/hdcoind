Require Import Coq.Program.Syntax.
Require Export ZArith.
Require Import Coq.Program.Basics.
Require Import SetoidTactics.
Require Import SetoidClass.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.

Local Open Scope char.
Local Open Scope bool.
Local Open Scope Z.


Definition ascii_of_Z (v:Z) : ascii := ascii_of_nat (Z.to_nat v).
Definition Z_of_ascii (c: ascii) : Z := Z.of_nat (nat_of_ascii c).
Coercion Z_of_ascii : ascii >-> Z.

Fixpoint seqZ (x: Z) (len: nat) :=
  match len with
  | O => nil
  | S len' => cons x (seqZ (1+x) len')
  end.

Fixpoint list_of_string (s: string) : list ascii :=
  match s with
  | EmptyString => nil
  | String c s' => c :: list_of_string s'
  end.

Lemma list_of_string_empty:
  list_of_string "" = nil.
Proof.
  reflexivity.
Qed.

Lemma list_of_string_cons: forall c s,
  list_of_string (String c s) = c::list_of_string s.
Proof.
  reflexivity.
Qed.

Lemma list_of_string_app: forall s1 s2,
  list_of_string (append s1 s2) = list_of_string s1 ++ list_of_string s2.
Proof.
  intros.
  induction s1; simpl;
    congruence.
Qed.

Definition array_ptrs (a: Z) (v: list Z) :=
  List.combine (seqZ a (length v)) v.

  Lemma array_ptrs_nil: forall a,
    array_ptrs a nil = nil.
  Proof. reflexivity. Qed.

  Lemma array_ptrs_cons: forall a v l,
    array_ptrs a (v::l) = (a,v)::array_ptrs (1+a) l.
  Proof. reflexivity. Qed.

  Lemma array_ptrs_app: forall a l1 l2,
    array_ptrs a (l1++l2) = array_ptrs a l1 ++ array_ptrs (a+Z.of_nat (length l1)) l2.
  Proof.
    intros a l1; revert a.
    induction l1; intros.
    * simpl (_+_).
    rewrite Z.add_0_r.
    reflexivity.
    * simpl (length _).
    rewrite <-!app_comm_cons, !array_ptrs_cons, Nat2Z.inj_succ.
    rewrite IHl1.
    rewrite Z.add_succ_r, !app_comm_cons, Z.add_1_l, Z.add_succ_l.
    reflexivity.
  Qed.

  Definition str_len (s: string) := length (list_of_string s).

  Lemma str_len_empty:
    str_len ""%string = 0%nat.
  Proof. reflexivity. Qed.

  Lemma str_len_cons: forall c s,
    str_len (String c s) = S (str_len s).
  Proof. reflexivity. Qed.

  Lemma str_len_app: forall s1 s2,
    str_len (append s1 s2) = (str_len s1 + str_len s2)%nat.
  Proof.
    unfold str_len; intros.
    rewrite list_of_string_app, app_length.
    reflexivity.
  Qed.

  Lemma list_of_string_length: forall s,
    length (list_of_string s) = str_len s.
  Proof. reflexivity. Qed.

  Lemma map_nil_iff: forall A B (f: A->B),
    map f nil = nil.
  Proof. reflexivity. Qed.

  Lemma map_cons_iff: forall A B (f: A->B) x l,
    map f (x::l) = f x :: map f l.
  Proof. reflexivity. Qed.

  Lemma cons_length: forall A (x:A) l,
    length (x::l) = S (length l).
  Proof. reflexivity. Qed.

  Lemma nil_length: forall A,
    length (@nil A) = O.
  Proof. reflexivity. Qed.

Hint Rewrite list_of_string_empty str_len_empty map_nil_iff nil_length array_ptrs_nil : lists.
Hint Rewrite list_of_string_cons str_len_cons map_cons_iff cons_length array_ptrs_cons : lists.
Hint Rewrite list_of_string_app str_len_app map_app app_length array_ptrs_app : lists.
Hint Rewrite map_length Z.add_0_r : lists.
Hint Rewrite Nat2Z.inj_succ Z.add_succ_r Z.add_1_l Z.add_succ_l Nat2Z.inj_add : lists.


  Definition is_upperZ (c: Z) : bool :=
    if (64 <? c) && (c <? 91) then
      true
    else
      false.

  Definition is_lowerZ (c: Z) : bool :=
    if (96 <? c) && (c <? 123) then
      true
    else
      false.

  Definition is_letterZ (c: Z) : bool := is_upperZ c || is_lowerZ c.

  Definition is_upper (c: ascii) : bool := is_upperZ c.
  Definition is_lower (c: ascii) : bool := is_lowerZ c.
  Definition is_letter (c: ascii) : bool := is_letterZ c.

  Definition getd (o:nat) (s:string) default :=
    match get o s with
    | Some c => c
    | None => default
    end.

  Ltac mcase_eq_clean:=
    match goal with
    | _ => discriminate
    | H1: Some _ = Some _ |- _ => inversion H1; subst; clear H1
    | H1: inl _ = inl _ |- _ => inversion H1; subst; clear H1
    | H1: inr _ = inr _ |- _ => inversion H1; subst; clear H1
    | H1: _ =? _ = true |- _ => rewrite Z.eqb_eq in H1
    | H1: _ =? _ = false |- _ => rewrite Z.eqb_neq in H1
    end.

  Ltac intro_subst:=
    repeat match goal with
    | |- ?x = _ -> _ => is_var x; intro; subst x
    | |- _ = ?x -> _ => is_var x; intro; subst x
    | |- _ = _ -> _ => let H:= fresh "H" in intro H; rewrite ?H in * |- *
    | |- forall _, _ => intro
    | |- _ -> _ => intro
    end.

  Ltac mcase_eq_term x:=
    match x with
    | appcontext[match ?t with _=>_ end] => case_eq t; intro_subst; repeat mcase_eq_clean
    end.

  Ltac mcase_eq_term_depth x:=
    match x with
    | appcontext[match ?t with _=>_ end] => mcase_eq_term_depth t
    | appcontext[match ?t with _=>_ end] => case_eq t; intro_subst; repeat mcase_eq_clean
    end.

  Tactic Notation "mcase_eq":=
    match goal with |- ?t => mcase_eq_term t end.
  Tactic Notation "mcase_eq" "in" hyp(H):=
    match type of H with ?t => mcase_eq_term t end.
  Tactic Notation "mcase_eq" "in" "*":=
    match goal with
    | |- ?t => mcase_eq_term t
    | H1: ?t |- _ => mcase_eq_term t
    end.
  Tactic Notation "mcase_eq!":=
    match goal with |- ?t => mcase_eq_term_depth t end.
  Tactic Notation "mcase_eq!" "in" hyp(H):=
    match type of H with ?t => mcase_eq_term_depth t end.
  Tactic Notation "mcase_eq!" "in" "*":=
    match goal with
    | |- ?t => mcase_eq_term_depth t
    | H1: ?t |- _ => mcase_eq_term_depth t
    end.

  Lemma N_of_digits_inv: forall l1 l2,
    N_of_digits l1 = N_of_digits l2 ->
    length l1 = length l2 ->
    l1 = l2.
  Proof.
    induction l1; destruct l2; simpl; intros; auto;
      repeat mcase_eq in *.
    * erewrite IHl1; eauto.
    * rewrite !N.add_1_l in *.
    apply N.succ_inj in H.
    inversion H; subst; clear H.
    erewrite IHl1; eauto.
    * erewrite IHl1; eauto.
    * inversion H; subst; clear H.
    erewrite IHl1; eauto.
  Qed.

  Lemma nat_of_ascii_inv: forall c1 c2,
    nat_of_ascii c1 = nat_of_ascii c2 ->
    c1 = c2.
  Proof.
    unfold nat_of_ascii, N_of_ascii; intros.
    apply Nnat.N2Nat.inj in H.
    destruct c1, c2.
    apply N_of_digits_inv in H; auto.
    inversion H; subst; clear H.
    reflexivity.
  Qed.

  Lemma Z_of_ascii_inv: forall c1 c2,
    Z_of_ascii c1 = Z_of_ascii c2 ->
    c1 = c2.
  Proof.
    unfold Z_of_ascii; intros.
    apply Nat2Z.inj in H.
    apply nat_of_ascii_inv in H; auto.
  Qed.

  Lemma Z_of_ascii_neq: forall c1 c2,
    c1 <> c2 ->
    Z_of_ascii c1 <> Z_of_ascii c2.
  Proof.
    intros; intro; apply H; auto using Z_of_ascii_inv.
  Qed.

  Lemma ascii_of_Z_id: forall c,
    ascii_of_Z (Z_of_ascii c) = c.
  Proof.
    unfold ascii_of_Z, Z_of_ascii; intros.
    rewrite Nat2Z.id.
    apply ascii_nat_embedding.
  Qed.

  Lemma is_letterZ_of_ascii: forall c,
    is_letterZ (Z_of_ascii c) = is_letter c.
  Proof. reflexivity. Qed.

  Lemma is_upperZ_of_ascii: forall c,
    is_upperZ (Z_of_ascii c) = is_upper c.
  Proof. reflexivity. Qed.

  Lemma is_lowerZ_of_ascii: forall c,
    is_lowerZ (Z_of_ascii c) = is_lower c.
  Proof. reflexivity. Qed.

  Lemma is_letterZ_eq: forall c,
    is_letterZ c = is_upperZ c || is_lowerZ c.
  Proof.
    unfold is_letterZ, is_lowerZ, is_upperZ; intros.
    repeat match goal with
      |- appcontext[?a <? ?b] => case_eq (a <? b); intros
      end;
      simpl; try reflexivity.
  Qed.

  Lemma is_lowerZ_eq: forall c,
    is_lowerZ c = is_letterZ c && negb (is_upperZ c).
  Proof.
    unfold is_letterZ, is_lowerZ, is_upperZ; intros.
    repeat match goal with
      |- appcontext[?a <? ?b] => case_eq (a <? b); intros
      end;
      simpl; try reflexivity.
    rewrite Z.ltb_lt in *.
    omega.
  Qed.

  Lemma is_upperZ_eq: forall c,
    is_upperZ c = is_letterZ c && negb (is_lowerZ c).
  Proof.
    unfold is_letterZ, is_lowerZ, is_upperZ; intros.
    repeat match goal with
      |- appcontext[?a <? ?b] => case_eq (a <? b); intros
      end;
      simpl; try reflexivity.
    rewrite Z.ltb_lt in *.
    omega.
  Qed.

  Lemma is_letter_eq: forall c,
    is_letter c = is_upper c || is_lower c.
  Proof.
    intros; apply is_letterZ_eq.
  Qed.

  Lemma is_lower_eq: forall c,
    is_lower c = is_letter c && negb (is_upper c).
  Proof.
    intros; apply is_lowerZ_eq.
  Qed.

  Lemma is_upper_eq: forall c,
    is_upper c = is_letter c && negb (is_lower c).
  Proof.
    intros; apply is_upperZ_eq.
  Qed.

  Lemma negb_orb_cancel_l: forall b,
    negb b || b = true.
  Proof. unfold orb, negb; simpl; intros; repeat mcase_eq in *; auto. Qed.

  Lemma negb_orb_cancel_r: forall b,
    b || negb b = true.
  Proof. unfold orb, negb; simpl; intros; repeat mcase_eq in *; auto. Qed.





