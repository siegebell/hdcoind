Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.



  Ltac thegoal:= match goal with |- ?G => constr:G end.

  Ltac idtac1 x:= idtac.
  Ltac idtac2 x y:= idtac.

  Definition rel_disj {A B :Type} (R1 R2: A->B->Prop) : A->B->Prop :=
    fun x y => R1 x y \/ R2 x y.

  Arguments rel_disj {_ _} _ _ _ _ /.
  Arguments flip {_ _ _} _ _ _ /.

Ltac dup:= match goal with |- ?g => cut g; [ intros _ | ] end.

Tactic Notation "if_ltac_sucess_then_else_fail" tactic(tac1) tactic(tac2):=
  first [ first [ dup; [tac1; fail 1 | fail 1] | fail 2 ] | tac2 ].

(* only performs eassumption if there is exactly one hypoothesis that is able to solve the goal *)
Ltac eassumption_unique := idtac; match goal with
| _ => assumption
| H1: ?P |- _ =>
  match type of P with Prop =>
  (* fail if there is more than one way to discharge the goal by assumption *)
  if_ltac_sucess_then_else_fail
    solve[exact H1]
    (clear H1; if_ltac_sucess_then_else_fail eassumption (fail 3))
  end
| _ => eassumption
end.


  Ltac solve_relation:=
    solve [
    intros;
    match goal with
    | |- exists _, _ => eexists; try solve [solve_relation]
    | |- _/\_ =>
      first
      [ split; solve[solve_relation]
      | split; [ | solve[solve_relation]]; solve[solve_relation]
      ]
    | |- _\/_ =>
      first
      [ left; solve[solve_relation]
      | right; solve[solve_relation]
      ]
    | _ => apply eq_refl
    | _ => eassumption_unique
    | _ => symmetry; eassumption_unique
    | _ => reflexivity
    | _ => eassumption
    | _ => solve[auto]
    | _ => congruence
    | _ => progress red; solve_relation
    end].



  Class CoIndRelation (T: Prop) := { coind_rel : Prop }.
  Arguments coind_rel _ {_}.
  Ltac coind_rel_match_Prop T := match eval cbv beta in T with
     | ?A -> ?B => refine {| coind_rel := A /\ coind_rel B |}
     | forall x : ?A, @?B x => refine {| coind_rel := exists x : A, coind_rel (B x) |}
     | exists x : ?A, @?B x => refine {| coind_rel := forall x : A, coind_rel (B x) |}
     | ?A /\ ?B => refine {| coind_rel := coind_rel A \/ coind_rel B |}
     | ?A \/ ?B => refine {| coind_rel := coind_rel A /\ coind_rel B |}
     | ?T' => refine {| coind_rel := T' |}
   end .
  Global Hint Extern 100 (CoIndRelation ?T) => coind_rel_match_Prop T : typeclass_instances. 

  Class CoRelation (T:Type) := {coind_co_rel (x:T): Prop}.
  Arguments coind_co_rel {_} {_} _.

  Definition coind_rel_singleton {A} x : @CoRelation A :=
    {|coind_co_rel x' := x=x' |}.
  Definition coind_rel_1 {A} x : @CoRelation A :=
    {|coind_co_rel x' := x=x' |}.
  Definition coind_rel_2 {A B} x y : @CoRelation (A*B) :=
    {|coind_co_rel a := let '(x',y'):= a in x=x' /\ y=y' |}.
  Definition coind_rel_3 {A B C} x y z : @CoRelation (A*B*C) :=
    {|coind_co_rel a := let '(x',y',z'):= a in x=x' /\ y=y' /\ z=z'|}.

Ltac infer_coind_relation G R :=
  (let t := (eval simpl in (fun x y z => let co_rel:= coind_rel_3 x y z in coind_rel G)) in
    pose t as R)
  ||
  (let t := (eval simpl in (fun x y => let co_rel:= coind_rel_2 x y in coind_rel G)) in pose t as R)
  ||
  (let t := (eval simpl in (fun x => let co_rel:= coind_rel_1 x in coind_rel G)) in pose t as R).

  Class CoIndPrinciple {A} (coind_relation:A) (T:Prop) :=
  { coind_principle_type: Type
  ; coind_principle: coind_principle_type
  }.

  Arguments coind_principle {_} _ _ {_}.

  Ltac intro_names cont' :=
    let nil_name tac1 tac2 :=
      idtac
      in
    let intro_name a x renames tac1 tac2 :=
      tac1 a x; renames tac1 tac2; tac2 a x
      in
    let rec helper renames cont:=
      lazymatch goal with
      | |- forall a:?A, _ =>
        let x:=fresh "XX" in intro x;
        helper ltac:(intro_name a x renames) cont
      | |- ?g =>
        cont renames
      end in
    helper ltac:nil_name cont'.

  Ltac eval_replace a b C :=
    match C with
    | context A[a] =>
       let C':= context A[b] in
       eval_replace a b C'
    | _ =>
      constr:C
    end.

  Class NormalizeProp (T: Prop) := { norm_Prop : Prop }.
  Arguments norm_Prop _ {_}.
  Ltac norm_Prop_match_Prop T := match eval cbv iota zeta beta delta [norm_Prop] in T with
     | (exists x:?C, ?A) -> ?B => refine {| norm_Prop:= norm_Prop (A -> B) |}
     | (exists x:?C, @?A x) -> ?B => refine {| norm_Prop:= forall x:C, norm_Prop (A x -> B) |}
     | ?A /\ ?B -> ?C => refine {| norm_Prop := norm_Prop (A -> norm_Prop (B -> C)) |}
     | ?a = ?b -> ?B =>
       is_var a; let B':= eval_replace a b B in
       refine {| norm_Prop := B' |}
     | ?a = ?b -> ?B =>
       is_var b; let B':= eval_replace b a B in
       refine {| norm_Prop := B' |}
     | ?A -> ?B => refine {| norm_Prop:= norm_Prop A -> norm_Prop B |}
     | forall x : ?A, @?B x =>
       let B':= eval cbv beta iota delta [norm_Prop] in (forall x : A, norm_Prop (B x)) in
       match B' with
       | _ -> ?C => refine {| norm_Prop := C |}
       | forall _, _ => refine {| norm_Prop := B' |}
       end
     | ?T' => refine {| norm_Prop := T' |}
   end.
  Global Hint Extern 100 (NormalizeProp ?T) => norm_Prop_match_Prop T : typeclass_instances. 

  Ltac norm_Prop_ H :=
    let T:= type of H in
    let t:= eval cbv beta iota delta [norm_Prop] in (norm_Prop T) in
    cut (t);
    [ clear H; intro H
    | clear -H;
      intros; apply H;
      solve_relation
    ].
  Tactic Notation "norm_Prop" "in" hyp(H) :=
    norm_Prop_ H.

  Ltac intros_norm_Prop:=
    cbv beta;
    repeat match goal with
    | |- ?A -> ?B =>
      let H1:= fresh "H" in
      intro H1;
      norm_Prop in H1
    | |- forall _, _ =>
      intro
    end.

  Ltac coind_ naming_cont:=
    let R2 := fresh "R" in
    infer_coind_relation thegoal R2;
    let apply_coind_principle R:=
      let G:= thegoal in
      (let t := eval simpl in (coind_principle R G) in eapply t)
    in
    intro_names ltac:(fun names => 
      apply_coind_principle R2;
      try match goal with
      | |- appcontext[R2 _] =>
        subst R2;
        cbv beta;
        solve_relation
      | _ =>
        names ltac:(fun a x => try clear x) idtac2;
        subst R2;
        intros_norm_Prop;
        naming_cont names
      end).
  Tactic Notation "coind":=
    coind_ ltac:(fun names => idtac).
  Tactic Notation "coind" "naming" tactic(naming_cont):=
    coind_ naming_cont.

  Tactic Notation "coind" "using" constr(principle) "naming" tactic(naming_cont):=
    refine (let _ := principle in _);
    match goal with
    | P:= _ |- _ =>
      coind_ naming_cont;
      subst P
    end.
  Tactic Notation "coind" "using" constr(principle):=
    coind using principle naming idtac1.





  Class SubstConclusion (T: Prop) := { subst_conclusion : Prop }.
  Arguments subst_conclusion _ {_}.
  Ltac subst_conclusion_match_Prop T := match eval cbv beta in T with
     | ?A -> ?B => refine {| subst_conclusion:= A -> subst_conclusion B |}
     | forall x : ?A, @?B x => refine {| subst_conclusion := forall x : A, subst_conclusion (B x) |}
     | ?T' => refine {| subst_conclusion := T' |}
   end .
  Global Hint Extern 100 (SubstConclusion ?T) => subst_conclusion_match_Prop T : typeclass_instances. 


  Ltac intro_relation_with_names names:=
      let p := fresh "p__" in
      let q := fresh "q__" in
      let HH := fresh "HH__" in
      intros p q HH;
      names ltac:idtac2 ltac:(fun a x => destruct HH as [a HH] || destruct HH as [? HH]);
      destruct HH as [??];
      subst p q.


Definition impred_gfp {A B:Type} (RR: (A->B->Prop)->Prop) p q : Prop:=
  exists R: A->B->Prop, R p q /\ RR R.

Lemma subrelation_impred_gfp: forall {A:Type} (RR: relation A->Prop) (R: relation A),
  RR R ->
  subrelation R (impred_gfp RR).
Proof.
  firstorder auto.
Qed.

