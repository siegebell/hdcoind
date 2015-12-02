Require Import Coq.Program.Syntax.
Require Export ZArith.
Require Import Coq.Program.Basics.
Require Import SetoidTactics.
Require Import SetoidClass.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.

Require Import HDI.Util.

Local Open Scope Z.

Inductive operation : Set :=
  | read (a: Z)
  | write (a: Z) (v: Z).

CoInductive stmt : Set :=
  | ret: Z -> stmt
  | abort: stmt
  | act: operation -> stmt
  | bind: stmt -> (Z -> stmt) -> stmt.

Delimit Scope stmt with stmt.
Bind Scope stmt with stmt.

Notation "s1 >>= s2" :=
  (bind s1%stmt s2%stmt)
  (right associativity, at level 41)
  : stmt.
Notation "s1 >> s2" :=
  ((s1 >>= (fun _ => s2))%stmt)
  (right associativity, at level 41)
  : stmt.
Notation "x <- a ; s" :=
  (bind a%stmt (fun x => s%stmt))
  (right associativity, at level 41)
  : stmt.
Notation "a ;; s" :=
  (bind a%stmt (fun _ => s%stmt))
  (right associativity, at level 41)
  : stmt.
Coercion act : operation >-> stmt.

Goal (forall s1 s2 k, x <- s1; s2;; k x = bind s1 (fun x => bind s2 (fun _ => k x)))%stmt. intros; reflexivity. Abort.


  Definition unfold_stmt (s: stmt) :=
    match s with
    | ret v => ret v
    | abort => abort
    | act o => act o
    | bind s k => bind s k
    end.

  Lemma unfold_stmt_eq: forall s,
    s = unfold_stmt s.
  Proof. destruct s; reflexivity. Qed.

