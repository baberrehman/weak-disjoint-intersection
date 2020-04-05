Require Import String.
Require Import STLC.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import Program.Equality.
Require Import TypingFlags.Loader.

Module CoherenceTop
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

  
Module ST := TLC(VarTyp)(set).
Import ST.


(* Notes:

The syntax is encoded using Charguéraud's Locally nameless representation:

http://www.chargueraud.org/softs/ln/

We annotate the Coq theorems with the correnposing lemmas/theorems in the paper. 
The reader can just look for:

Lemma 4

for example, to look for the proof of lemma 4 in the paper.

All lemmas and theorems are complete: there are no uses of admit or Admitted,
with the exceptions of "tlam" and "tylam" due to a technical limitation.

*)


(* Types *)

Inductive PTyp : Type :=
  | PInt : PTyp
  | Fun : PTyp -> PTyp -> PTyp
  | And : PTyp -> PTyp -> PTyp
  | TopT : PTyp.

Fixpoint ptyp2styp (t : PTyp) : STyp :=
  match t with
    | PInt => STInt 
    | Fun t1 t2 => STFun (ptyp2styp t1) (ptyp2styp t2)
    | And t1 t2 => STTuple (ptyp2styp t1) (ptyp2styp t2)
    | TopT => STUnitT
  end.

Inductive Atomic : PTyp -> Prop :=
  | AInt : Atomic PInt
  | AFun : forall t1 t2, Atomic (Fun t1 t2).

(* Subtyping relation *)

Inductive sub : PTyp -> PTyp -> Prop :=
  | SInt : sub PInt PInt
  | SFun : forall o1 o2 o3 o4, sub o3 o1 -> sub o2 o4 -> 
     sub (Fun o1 o2) (Fun  o3 o4)
  | SAnd1 : forall t t1 t2, sub t t1 -> sub t t2 -> 
     sub t (And  t1 t2)
  | SAnd2 : forall t t1 t2, sub t1 t ->
     sub (And  t1 t2) t
  | SAnd3 : forall t t1 t2, sub t2 t ->
     sub (And  t1 t2) t
  | STop : forall t, sub t TopT.

Notation "'|' t '|'" := (ptyp2styp t) (at level 60).

Hint Resolve SInt SFun SAnd1 SAnd2 SAnd3 STop.

Lemma invAndS1 : forall t t1 t2, sub t (And t1 t2) -> sub t t1 /\ sub t t2.
Proof.
  intro t; induction t; intros.
(* Case Int *)
  inversion H. auto.
(* Case Fun *)
  inversion H. auto.
(* Case And *)
  inversion H; auto.
  assert (sub t1 t0 /\ sub t1 t3).
  auto.
  split.
  destruct H4; apply SAnd2; auto.
  destruct H4; apply SAnd2; auto.
  assert (sub t2 t0 /\ sub t2 t3).
  auto.
  split.
  destruct H4; apply SAnd3; auto.
  destruct H4; apply SAnd3; auto.
(* Top cases *)
  inversion H. auto.
Qed.

Lemma sub_refl: forall A, sub A A.
Proof.
  intros.
  induction A; eauto.
Qed.

Hint Resolve sub_refl.

Lemma sub_transitivity: forall B A C, sub A B -> sub B C -> sub A C.
Proof.
  induction B; intros;
  generalize H0 H; clear H0; clear H; generalize A; clear A.
  - induction C; intro; intro; try (inversion H0); auto.
  - induction C; intro; intro; try (inversion H0); auto.
    induction A; intro; try (inversion H6); eauto.
  - intros; apply invAndS1 in H; destruct H;
    dependent induction H0; eauto.
  - induction C; intro; intro; try (inversion H0); auto.
Qed.

Hint Resolve invAndS1 sub_refl.


Inductive TopLike : PTyp -> PTyp -> PTyp -> Prop :=
  | TLTop  : forall A B, TopLike A B TopT
  | TLAnd  : forall A B C D, TopLike C D A -> TopLike C D B -> TopLike C D (And A B)
  | TLFun  : forall A B C D, TopLike C D B -> TopLike C D (Fun A B)
  | TLFunAnd : forall A B C D A1 A2, sub C (Fun A1 B) -> sub D (Fun A2 B) -> not (sub A1 A2) -> not (sub A2 A1) ->
   sub A (And A1 A2) -> TopLike C D (Fun A B).

(*
TLFunAnd states that output of two functions must be same and different input.
*)

Hint Resolve TLTop TLAnd TLFun TLFunAnd.


(* Disjointness: Specification *)

Definition OrthoS (A B: PTyp) := forall C, sub A C -> sub B C -> (TopLike A B C).

(* Disjointness: Implementation *)

(*Set Guard Checking.
Print Typing Flags.*)

Inductive Ortho : PTyp -> PTyp -> Prop :=
  | OTop : forall t1, Ortho t1 TopT
  | OTop1 : forall t1, Ortho TopT t1
  | OAnd1 : forall t1 t2 t3, Ortho t1 t3 -> Ortho t2 t3 -> Ortho (And t1 t2) t3
  | OAnd2 : forall t1 t2 t3, Ortho t1 t2 -> Ortho t1 t3 -> Ortho t1 (And t2 t3)
  | OIntFun : forall t1 t2, Ortho PInt (Fun t1 t2)
  | OFunInt : forall t1 t2, Ortho (Fun t1 t2) PInt
  | OFun   : forall t1 t2 t3 t4, Ortho t2 t4 -> Ortho (Fun t1 t2) (Fun t3 t4)
  | OFunA  : forall t1 t2 t3 t4, Ortho t1 t3 -> Ortho (Fun t1 t2) (Fun t3 t4).

Hint Resolve OTop OTop1 OAnd1 OAnd2 OIntFun OFunInt OFun OFunA.

(* Well-formed types *)

Inductive WFTyp : PTyp -> Prop := 
  | WFInt : WFTyp PInt
  | WFFun : forall t1 t2, WFTyp t1 -> WFTyp t2 -> WFTyp (Fun t1 t2)
  | WFAnd : forall t1 t2, WFTyp t1 -> WFTyp t2 -> OrthoS t1 t2-> WFTyp (And t1 t2)
  | WFTop : WFTyp TopT.


(* Lemmas needed to prove soundness of the disjointness algorithm *)

Lemma sym_top_like: forall A B C, TopLike A B C -> TopLike B A C.
intros. dependent induction H.
apply TLTop.
apply TLAnd. auto. auto.
apply TLFun. auto.
apply TLFunAnd with (A1:=A2) (A2:=A1); auto.
apply invAndS1 in H3. destruct H3.
apply SAnd1; auto.
Defined.

Lemma ortho_sym : forall {A B: PTyp}, OrthoS A B -> OrthoS B A.
Proof.
unfold OrthoS.
intros.
apply sym_top_like. auto.
Defined.

Lemma toplike_and : forall A B C D, TopLike A C D -> TopLike B C D ->
    TopLike (And A B) C D.
Proof.
intros.
induction D; eauto.
inversion H.
apply TLFun.
apply IHD2.
inversion H; eauto.
admit.
admit.
apply TLAnd; auto.
apply IHD1.
inversion H; auto.
inversion H0; auto.
apply IHD2.
inversion H; auto.
inversion H0; auto.
Admitted.

(*
Counter Example for toplike_and and ortho_and:
A = Int -> Int
B = Int -> Int
C = char -> Int
D = Int & char -> Int

toplike_and and ortho_and are not valid lemmas.

*)

Lemma ortho_and : forall {A B C}, OrthoS A C -> OrthoS B C -> OrthoS (And A B) C.
Proof.
intros.
unfold OrthoS. intros.
dependent induction H1.
 - apply TLAnd.
   apply IHsub1; auto.
   apply invAndS1 in H2. destruct H2. auto.
   apply IHsub2; auto.
   apply invAndS1 in H2. destruct H2. auto.
 - unfold OrthoS in H.
   unfold OrthoS in H0.
   assert (TopLike A C t0); auto.
   dependent induction H3; eauto.
   apply TLAnd.
   apply toplikeinv1; eauto.
   apply H0; eauto. admit. apply invAndS1 in H2. destruct H2; auto.
   apply toplikeinv1; eauto.
   apply H0; eauto. admit. apply invAndS1 in H2. destruct H2; auto.
   apply toplikeinv1.
   apply H; eauto.
   apply H0; eauto.
   admit.
 - unfold OrthoS in *.
   apply toplikeinv1; eauto.
   apply H; eauto.
   assert (TopLike B C t0); eauto.
  admit.
 - apply TLTop.

(*admit.
apply TLFun.
apply IHC0_2.
apply SAnd2.
admit.
admit.

apply TLAnd.
apply IHC0_1.
apply SAnd2.
apply invAndS1 in H1. destruct H1.
admit.
apply invAndS1 in H2. destruct H2. auto.
apply IHC0_2.
apply SAnd2.
apply invAndS1 in H1. destruct H1.
admit.
apply invAndS1 in H2. destruct H2. auto.
apply TLTop.*)
Admitted.

Lemma applyOrthoS : forall {A B}, OrthoS A B -> forall C, sub A C -> sub B C -> TopLike A B C.
Proof.
intros. destruct H with (C:=C); auto.
Defined.

(*Lemma invTopLike {A B}: forall C, TopLike A B C -> OrthoS A B -> sub A C /\ sub B C.
Proof.
intros. split.
 - dependent induction H; auto.
  + assert (sub C B); auto.
    unfold OrthoS in H0.
  + dependent induction H.
  + dependent induction H.
    apply IHTopLike; auto. admit.
    apply invAndS1 in H3. destruct H3.
    inversion H. subst.
    apply SFun; auto.
    admit.
    subst. apply SAnd2. admit.
    subst. apply SAnd3. admit.
  + inversion H.
    apply SAnd1.
    apply IHC1; auto.
    apply IHC2; auto.
 - dependent induction C; auto.
  + dependent induction H.
  + dependent induction H.
    apply IHTopLike; auto. admit.
    apply invAndS1 in H3. destruct H3.
    inversion H0. subst.
    apply SFun; auto.
    admit.
    subst. apply SAnd2. admit.
    subst. apply SAnd3. admit.
  + inversion H.
    apply SAnd1.
    apply IHC1; auto.
    apply IHC2; auto.
Admitted.*)

Lemma invOrthos: forall t1 t2 t3, OrthoS t1 (And t2 t3) -> OrthoS t1 t2 /\ OrthoS t1 t3.
intros. split.
 - unfold OrthoS. intros.
   unfold OrthoS in H.
   assert (TopLike t1 (And t2 t3) C).
   apply H; auto.
   dependent induction H2; eauto.
    + apply TLAnd.
      eapply IHTopLike1; auto.
      apply invAndS1 in H0. destruct H0. auto.
      apply invAndS1 in H1. destruct H1. auto.
      eapply IHTopLike2; auto.
      apply invAndS1 in H0. destruct H0. auto.
      apply invAndS1 in H1. destruct H1. auto.
    + eapply TLFun.
      assert (TopLike C (And t2 t3) (Fun A B)); eauto.
      eapply IHTopLike; eauto.
      admit.
      admit.
    + eapply TLFunAnd with (A1:=A1) (A2:=A2); eauto.
      admit.
 - unfold OrthoS. intros.
   unfold OrthoS in H.
   assert (TopLike t1 (And t2 t3) C).
   apply H; auto.
   dependent induction H2; eauto.
   + apply TLAnd.
     eapply IHTopLike1; auto.
     apply invAndS1 in H0. destruct H0. auto.
     apply invAndS1 in H1. destruct H1. auto.
     eapply IHTopLike2; auto.
     apply invAndS1 in H0. destruct H0. auto.
     apply invAndS1 in H1. destruct H1. auto.
    + apply TLFun; eauto.
      eapply IHTopLike; auto.
      admit. admit.
    + eapply TLFunAnd with (A1:=A1) (A2:=A2); auto.
      admit.
Admitted.

(* Disjointness algorithm is complete: Theorem 8 *)

Lemma ortho_func {t1 t2 t3 t4} :
      Ortho (Fun t1 t2) (Fun t3 t4) -> Ortho t1 t3 \/ Ortho t2 t4.
Proof.
intros.
inversion H.
right. auto.
left. auto.
Qed.

(*
I think ortho_func is not correct. We may need to update
TopLike or the definition of ortho_func.
We have a rule which says input should be different.
But we do not have a rule for output types.
*)

Lemma orthos_func {t1 t2 t3 t4} : WFTyp t1 -> WFTyp t3 -> WFTyp t2 -> WFTyp t4 ->
      OrthoS (Fun t1 t2) (Fun t3 t4) -> OrthoS t1 t3 \/ OrthoS t2 t4.
Proof.
intros.
 - unfold OrthoS. right. intros.
   unfold OrthoS in H3.
   dependent induction C.
 + specialize (H3 (Fun (And t1 t3) PInt)).
  assert (TopLike (Fun t1 t2) (Fun t3 t4) (Fun (And t1 t3) PInt)).
  apply H3; eauto.
  dependent induction H6; eauto.
  dependent destruction H6.
  dependent destruction H9.
  dependent destruction H6.
  admit.
(* We can never prove that Int is TopLike *)
  + unfold OrthoS in H3.
    apply TLFun.
    apply IHC2.
    assert (TopLike (Fun t1 t2) (Fun t3 t4) (Fun (And t1 t3) ((Fun C1 C2)))).
    apply H3; eauto.
    admit.
    admit.
  + apply TLAnd.
    apply IHC1.
    apply invAndS1 in H4; destruct H4; auto.
    apply invAndS1 in H5; destruct H5; auto.
    apply IHC2.
    apply invAndS1 in H4; destruct H4; auto.
    apply invAndS1 in H5; destruct H5; auto.
  + apply TLTop.
Admitted. 

Lemma ortho_completness : forall t1, WFTyp t1 -> forall t2, WFTyp t2 -> OrthoS t1 t2 -> Ortho t1 t2.
Proof.
intros t1 wft1.
induction wft1; intros.
(* Case PInt *)
generalize H0. clear H0. induction H; intros.
unfold OrthoS in H0.
pose (H0 PInt SInt SInt). inversion t0.
apply OIntFun.
apply OAnd2. apply IHWFTyp1.
apply invOrthos in H2.
destruct H2; auto. 
apply invOrthos in H2.
destruct H2; auto. 
apply OTop.
(* Case Fun t1 t2 *)
induction H.
apply OFunInt.
(* Case Fun t1 t2 | Fun t0 t3 *)
apply orthos_func in H0.
destruct H0.
apply OFunA. auto.
apply OFun. apply IHwft1_2.
auto. auto. auto. auto. auto. auto.
(* Case t11 -> t12 _|_ t21 & t22 *)
apply OAnd2. apply IHWFTyp1.
unfold OrthoS.
intros.
apply invOrthos in H0. destruct H0. auto.
apply invOrthos in H0. destruct H0. auto.
(* Case t11 -> t12 _|_ T *)
apply OTop.
(* Case (t11 & t12) _|_ t2 *)
apply OAnd1.
apply IHwft1_1. auto.
apply ortho_sym in H1.
apply invOrthos in H1. destruct H1.
apply ortho_sym. auto.
apply IHwft1_2. auto.
apply ortho_sym in H1.
apply invOrthos in H1. destruct H1.
apply ortho_sym. auto.
apply OTop1.
Defined.


(* Unique subtype contributor: Lemma 4 *)

Lemma uniquesub : forall A B C, 
  OrthoS A B -> sub (And A B) C -> not (TopLike A B C) ->  not (sub A C /\ sub B C).
Proof.
intros. unfold OrthoS in H. unfold not. intros. destruct H2.
destruct H with (C:=C); auto.
Defined.

Lemma applyOrtho : forall {A B}, Ortho A B -> forall C, sub A C -> sub B C -> TopLike A B C.
intros.
apply applyOrthoS; auto.
unfold OrthoS. intros.
Admitted.


(* Soundness of the disjointness algorithm: Theorem 7 *)

Lemma ortho_soundness : forall (t1 t2 : PTyp), Ortho t1 t2 -> OrthoS t1 t2.
intros.
induction H.
(*Case t1 TopT*)
unfold OrthoS. intros.
induction C; intros. inversion H0. inversion H0.
apply TLAnd. apply IHC1.
apply invAndS1 in H. destruct H. auto.
apply invAndS1 in H0. destruct H0. auto.
apply IHC2.
apply invAndS1 in H. destruct H. auto.
apply invAndS1 in H0. destruct H0. auto.
apply TLTop.
(*Case TopT t1*)
unfold OrthoS. intros.
induction C. inversion H. inversion H.
apply TLAnd. apply IHC1.
apply invAndS1 in H. destruct H. auto.
apply invAndS1 in H0. destruct H0. auto.
apply IHC2.
apply invAndS1 in H. destruct H. auto.
apply invAndS1 in H0. destruct H0. auto.
apply TLTop.
(* Hard case *)
apply ortho_and; auto.
assert (OrthoS t2 t1). apply ortho_sym. apply IHOrtho1; auto.
assert (OrthoS t3 t1). apply ortho_sym. apply IHOrtho2; auto.
apply ortho_sym.
apply ortho_and; auto.
(* Case IntFun *)
unfold OrthoS.
induction C; intros. inversion H0. inversion H.
apply TLAnd. apply IHC1. inversion H. auto. inversion H0. auto.
apply IHC2. inversion H. auto. inversion H0. auto.
(* TopT *)
apply TLTop.
(* Case FunInt *)
unfold OrthoS.
induction C; intros. inversion H. inversion H0.
apply TLAnd.
apply IHC1.
inversion H. auto.
inversion H0. auto.
apply IHC2.
inversion H. auto.
inversion H0. auto.
(* TopT *)
apply TLTop.
(* FunFun *)
unfold OrthoS.
intros.
induction C. inversion H0.
assert (Ortho (Fun t1 t2) (Fun t3 t4)).
apply OFun. auto.
apply applyOrtho. auto. auto. auto.
apply TLAnd. apply IHC1. inversion H0. auto. inversion H1. auto.
apply IHC2. inversion H0. auto. inversion H1. auto.
apply TLTop.
(* FunFunA *)
unfold OrthoS.
intros.
induction C. inversion H0.
assert (Ortho (Fun t1 t2) (Fun t3 t4)).
apply OFunA. auto.
apply applyOrtho. auto. auto. auto. auto.
apply TLAnd. apply IHC1. inversion H0. auto. inversion H1. auto.
apply IHC2. inversion H0. auto. inversion H1. auto.
apply TLTop.
Defined.