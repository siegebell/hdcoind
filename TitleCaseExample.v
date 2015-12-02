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
Require HDI.HoareDoubles.
Require HDI.HoareDoublesI.

Local Open Scope Z.
Local Open Scope stmt.
Local Open Scope char.
Local Open Scope bool.

Section Implementation.

  CoFixpoint parseWS a : stmt:=
    x <- read a;
    if x =? zero then
      ret 1 (* Title Case *)
    else if x =? " " then
      parseWS (1+a)
    else if (negb (is_letterZ x)) || (is_upperZ x) then
      parseLetters (1+a)
    else
      ret 0 (* not type case *)
  with parseLetters (a:Z) :=
    x <- read a;
    if x =? zero then
      ret 1 (* Title Case *)
    else if x =? " " then
      parseWS (1+a)
    else if negb (is_letterZ x) || is_lowerZ x then
        parseLetters (1+a)
      else
        ret 0 (* cAps in woRd *).

  Definition isTitleCase := parseWS.

  Lemma unfold_parseWS: forall a,
    parseWS a =
    x <- read a;
    if x =? zero then
      ret 1 (* Title Case *)
    else if x =? " " then
      parseWS (1+a)
    else if (negb (is_letterZ x)) || (is_upperZ x) then
      parseLetters (1+a)
    else
      ret 0 (* not type case *).
  Proof. intros; rewrite (unfold_stmt_eq (parseWS a)); reflexivity. Qed.

  Lemma unfold_parseLetters: forall a,
    parseLetters a =
    x <- read a;
    if x =? zero then
      ret 1 (* Title Case *)
    else if x =? " " then
      parseWS (1+a)
    else if negb (is_letterZ x) || is_lowerZ x then
        parseLetters (1+a)
      else
        ret 0 (* cAps in woRd *).
  Proof. intros; rewrite (unfold_stmt_eq (parseLetters a)); reflexivity. Qed.

End Implementation.



Section Verification.

  Fixpoint is_title_case_ (in_word: bool) (s: string) {struct s} : bool :=
    match s with
    | String x s' =>
      if ascii_dec x zero then
        true (* Title Case *)
      else if ascii_dec x " " then
        is_title_case_ false s'
      else if in_word then
        if negb (is_letter x) || is_lower x then
          is_title_case_ true s'
        else
          false  (* cAps in woRd *)
      else
        let check_word x s :=
          if (negb (is_letter x)) || (is_upper x) then
            is_title_case_ true s'
          else
            false (* not type case *)
        in
        check_word x s'
    | empty => true (* Title Case *)
    end.
  Definition is_title_case s := is_title_case_ false s.

  Goal is_title_case "" = true. reflexivity. Abort.
  Goal is_title_case "  " = true. reflexivity. Abort.
  Goal is_title_case "67" = true. reflexivity. Abort.
  Goal is_title_case "A" = true. reflexivity. Abort.
  Goal is_title_case "z" = false. reflexivity. Abort.
  Goal is_title_case "Hello World" = true. reflexivity. Abort.
  Goal is_title_case "Hello world" = false. reflexivity. Abort.
  Goal is_title_case "hello World" = false. reflexivity. Abort.
  Goal is_title_case "HeLlo World" = false. reflexivity. Abort.
  Goal is_title_case "  Hello     World  " = true. reflexivity. Abort.
  Goal is_title_case "8ello World" = true. reflexivity. Abort.
  Goal is_title_case "8ellO World" = false. reflexivity. Abort.

  Lemma is_title_case_in_word: forall s,
    is_title_case_ true s = is_title_case (String "A" s).
  Proof. intros; reflexivity. Qed.

  Section HD.
    Import HoareDoubles.

    Lemma isTitleCase_ok: forall a s F k,
      |-{{a |->0 s && F}}  k (if is_title_case s then 1 else 0) ->
      |-{{a |->0 s && F}}  isTitleCase a >>= k.
    Proof.
    Abort.

  End HD.

  Import HoareDoublesI.
  Require Import CoInduction.


  Lemma parseLetters_ind_ok: forall (I: predicate heap -> stmt -> Prop) a s F k,
    I ||= {{a |->0 s && F}}  k (if is_title_case_ true s then 1 else 0) ->
    (forall a s0 s' F,
      append s0 s' = s ->
      I ||= {{a |->0 s' && F}}  k (if is_title_case_ false s' then 1 else 0) ->
      I ||- {{a |->0 s' && F}} (parseWS a >>= k)) ->
    I ||- {{a |->0 s && F}}  parseLetters a >>= k.
  Proof.
    intros I a s F k.
    intros Hsafe_k Hsafe_sws.
    revert a F Hsafe_k.
    induction s; simpl; intros.
    * rewrite unfold_parseLetters.
    step.
    mcase_eq.
    step; auto.
    * rewrite unfold_parseLetters.
    step.
    mcase_eq.
    { apply Z_of_ascii_inv in H; subst a.
      step; auto.
    }
    destruct (ascii_dec a zero); subst.
    congruence.
    destruct (ascii_dec a " "); subst.
    { rewrite Z.eqb_refl.
      rewrite str0_cons, (inter_comm ((1+a0) |->0 _)), <-!inter_assoc in Hsafe_k |- *.
      apply hd'_safe.
      eapply (Hsafe_sws (1+a0) " "%string s); auto.
    }
    rewrite (proj2 (Z.eqb_neq _ _)); [ | apply Z_of_ascii_neq; auto ].
    (*   else if negb (is_letterZ x) || is_lowerZ x *)
    rewrite is_letterZ_of_ascii, is_lowerZ_of_ascii.
    rewrite is_letter_eq in Hsafe_k |- *.
    rewrite Bool.negb_orb, Bool.orb_andb_distrib_l, negb_orb_cancel_l in Hsafe_k |- *.
    rewrite Bool.andb_true_r in Hsafe_k |- *.
    mcase_eq.
    { rewrite str0_cons, (inter_comm ((1+a0) |->0 _)), <-!inter_assoc in Hsafe_k |- *.
      apply hd'_safe.
      apply IHs; intros; auto.
      eapply Hsafe_sws with (s0:=String a s0); auto.
      subst s.
      reflexivity.
    }
    (*     else ret 0 >>= k *)
    step; assumption.
  Qed.

  Lemma parseWS_ind_ok: forall I a s F k,
    I ||= {{a |->0 s && F}}  k (if is_title_case_ false s then 1 else 0) ->
    I ||- {{a |->0 s && F}}  parseWS a >>= k.
  Proof.
    intros I a s F k Hsafe_k.
    revert Hsafe_k.
    remember (append EmptyString s) as s1.
    revert Heqs1.
    generalize EmptyString as s0.
    revert a s F.
    induction s1; simpl; intros; subst.
    * rewrite unfold_parseWS.
    destruct s0, s; try solve [inversion Heqs1].
    step.
    mcase_eq.
    step; auto.
    * rewrite unfold_parseWS.
    step.
    mcase_eq.
    { step; auto.
      repeat mcase_eq in *.
      destruct s0; inversion Heqs1; subst; eauto.
      apply Z_of_ascii_inv in H; subst; auto.
      apply Z_of_ascii_inv in H; subst; auto.
      simpl in H0; discriminate.
    }
    destruct s.
    compute in H; exfalso; eauto.
    rewrite str0_cons, (inter_comm ((1+a0) |->0 _)), <-!inter_assoc in Hsafe_k |- *.
    rewrite is_letterZ_of_ascii, is_upperZ_of_ascii.
    unfold is_title_case_ in Hsafe_k.
    fold is_title_case_ in Hsafe_k.
    destruct (ascii_dec a1 zero); subst.
    congruence.
    destruct (ascii_dec a1 " "); subst.
    { rewrite Z.eqb_refl.
      apply hd'_safe; eauto.
      destruct s0; inversion Heqs1; subst; eauto.
      eapply IHs1 with (s1:=""%string); auto.
      eapply IHs1 with (s2:= (s0++" ")%string); auto.
      clear.
      induction s0; simpl in *; congruence.
    }
    rewrite (proj2 (Z.eqb_neq _ _)); [ | apply Z_of_ascii_neq; auto ].
    repeat mcase_eq.
    apply hd'_safe, parseLetters_ind_ok; intros; subst; eauto.
    destruct s0; inversion Heqs1; subst; eauto.
    eapply IHs1 with (s1:=(s0++String a1 s2)%string); eauto.
    clear; induction s0; simpl in *; congruence.
    step; auto.
  Qed.




  Lemma parseLetters_ok: forall (I0 I: predicate heap -> stmt -> Prop) a s F k,
    I0 ||= {{a |->0 s && F}}  k (if is_title_case_ true s then 1 else 0) ->
    incl_inv I0 I ->
    (forall a s F,
      I0 ||= {{a |->0 s && F}}  k (if is_title_case_ false s then 1 else 0) ->
      I ||= {{a |->0 s && F}} parseWS a >>= k) ->
    I ||- {{a |->0 s && F}}  parseLetters a >>= k.
  Proof.
    intros I0 I a s F k.
    intros Hsafe_k HI0 Hsafe_sws.
    revert a s F Hsafe_k.
    hd_coind.
    (* x <- parseLetters a; k x *)
    rewrite unfold_parseLetters.
    (* x <- act (read a); *)
    step.
    (* (if x =? Z_of_ascii zero *)
    mcase_eq.
    (*  then ret 1 *)
    { rewrite HI0, H0 in Hsafe_k.
      destruct s; simpl in *.
      step; auto.
      apply Z_of_ascii_inv in H1; subst.
      simpl in *.
      step; auto.
    }
    destruct s.
    compute in H1; congruence.
    (*  else if x =? Z_of_ascii " " *)
    unfold is_title_case in Hsafe_k.
    simpl in Hsafe_k.
    destruct (ascii_dec a0 zero); subst.
    congruence.
    destruct (ascii_dec a0 " "); subst.
    (*   then parseWS (1 + a) *)
    { rewrite Z.eqb_refl.
      rewrite str0_cons, (inter_comm ((1+a) |->0 _)), <-!inter_assoc in Hsafe_k |- *.
      rewrite <-H0.
      apply Hsafe_sws; assumption.
    }
    rewrite (proj2 (Z.eqb_neq _ _)); [ | apply Z_of_ascii_neq; auto ].
    (*   else if negb (is_letterZ x) || is_lowerZ x *)
    rewrite is_letterZ_of_ascii, is_lowerZ_of_ascii.
    rewrite is_letter_eq in Hsafe_k |- *.
    rewrite Bool.negb_orb, Bool.orb_andb_distrib_l, negb_orb_cancel_l in Hsafe_k |- *.
    rewrite Bool.andb_true_r in Hsafe_k |- *.
    mcase_eq.
    (*     then parseLetters (1 + a) *)
    rewrite str0_cons, (inter_comm ((1+a) |->0 _)), <-!inter_assoc in Hsafe_k |- *.
    eauto.
    (*     else ret 0 >>= k *)
    rewrite <-H0, <-HI0.
    step; assumption.
  Qed.

  Lemma parseWS_ok: forall I a s F k,
    I ||= {{a |->0 s && F}}  k (if is_title_case_ false s then 1 else 0) ->
    I ||- {{a |->0 s && F}}  parseWS a >>= k.
  Proof.
    intros I a s F k Hsafe_k.
    revert a s F Hsafe_k.
    hd_coind.
    (* x <- parseWS a; k x *)
    rewrite unfold_parseWS.
    (* x <- read a *)
    step.
    (* if x =? Z_of_ascii zero *)
    mcase_eq.
    { (* then ret 1 *)
      rewrite H0 in Hsafe_k.
      destruct s; simpl in *.
      step; auto.
      apply Z_of_ascii_inv in H1; subst.
      simpl in *.
      step; auto.
    }
    destruct s.
    compute in H1; congruence.
    (* else if x =? " " *)
    rewrite str0_cons, (inter_comm ((1+a) |->0 _)), <-!inter_assoc in Hsafe_k |- *.
    simpl (is_title_case_ _ _) in Hsafe_k.
    rewrite is_letterZ_of_ascii, is_upperZ_of_ascii.
    destruct (ascii_dec a0 zero); subst.
    congruence.
    destruct (ascii_dec a0 " "); subst.
    (* then parseWS (1+a) *)
    rewrite Z.eqb_refl; auto.
    (* else if (negb (is_letterZ x)) || (is_upperZ x) *)
    rewrite (proj2 (Z.eqb_neq _ _)); [ | apply Z_of_ascii_neq; auto ].
    repeat mcase_eq.
    (* then parseLetters (1+a) *)
    apply hd'_safe, parseLetters_ok with (I0:=I); auto.
    (* else ret 0 (* not type case *) *)
    rewrite <-H0; step; assumption.
  Qed.



  Lemma isTitleCase_ok: forall I a s F k,
    I ||= {{a |->0 s && F}}  k (if is_title_case s then 1 else 0) ->
    I ||- {{a |->0 s && F}}  isTitleCase a >>= k.
  Proof.
    intros I a s F k Hsafe_k.
    unfold isTitleCase.
    apply parseWS_ok; assumption.
  Qed.


End Verification.
