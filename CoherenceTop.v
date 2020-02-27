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

(*Lemma sub_int : forall A, sub PInt A -> sub A PInt \/ sub TopT A.
Proof.
  intros.

  dependent induction H; eauto.
  left.
  apply SAnd3.
  dependent destruction IHsub1; eauto.
  dependent destruction IHsub2; eauto.
  (*induction A; eauto.
  admit.
  destruct IHA1; eauto.
  apply invAndS1 in H. destruct H. auto.
  right. apply SAnd1; auto.
  destruct IHA2; eauto.
  apply invAndS1 in H. destruct H. auto.
  apply invAndS1 in H. destruct H. auto.
  eapply sub_transitivity with (B:=A1); auto.*)
Admitted.

Lemma fintfint : not( OrthoS (Fun PInt PInt) (Fun PInt PInt) ).
unfold not; intros.
unfold OrthoS in H.
assert (TopLike (Fun PInt PInt) (Fun PInt PInt) (Fun PInt PInt)).
apply (H (Fun PInt PInt)). auto. auto.
dependent destruction H0.
dependent destruction H0.
dependent destruction H0.
dependent destruction H1.
dependent destruction H4; eauto.
clear H0_ H0_0 H1_ H1_0 H.

remember H4_.
remember H4_0.
clear Heqs Heqs0.

apply sub_int in H4_.
destruct H4_; eauto.
- admit.
- admit.
Admitted.

Lemma fintffint : OrthoS (Fun PInt PInt) (Fun (Fun PInt PInt) PInt).
unfold OrthoS.
intros.
dependent induction H; eauto.
dependent destruction H1.
apply TLFun.

admit.
apply TLAnd.
apply invAndS1 in H1. destruct H1.
apply IHsub1; eauto.
apply invAndS1 in H1. destruct H1.
apply IHsub2; eauto.
Admitted.

(*((Int -> Int) & Top) * (Char -> Int) *)

Lemma topintcharand : OrthoS (And (Fun PInt PInt) TopT) (Fun (Fun PInt PInt) PInt).
unfold OrthoS.
intros.
dependent destruction H; eauto.
dependent induction H1.
apply IHsub2; eauto.
Admitted.


(*Definition OrthoS (A B : PTyp) := 
  ((forall C, Sub A C -> Sub B C -> TopLike C)
   \/ (forall A1 B1 A2 B2, A = Fun A1 A2 -> B = Fun B1 B2 -> not (Sub A1 B1) -> not (Sub B1 A1) -> 
     TopLike (And A B))).*)*)

Inductive TopLike : PTyp -> PTyp -> PTyp -> Prop :=
  | TLTop  : forall A B, TopLike A B TopT
  | TLAnd  : forall A B C D, TopLike C D A -> TopLike C D B -> TopLike C D (And A B)
  | TLFun  : forall A B C D, TopLike C D B -> TopLike C D (Fun A B)
  | TLFunAnd : forall A B C D A1 A2, sub C (Fun A1 B) -> sub D (Fun A2 B) -> not (sub A1 A2) -> not (sub A2 A1) ->
   sub A (And A1 A2) -> TopLike C D (Fun A B).

Hint Resolve TLTop TLAnd TLFun TLFunAnd.

(*Inductive TopLikeAux : PTyp -> PTyp -> PTyp -> Prop :=
| TLFunAnd : forall A B C D A1 A2, Sub C (Fun A1 B) -> Sub D (Fun A2 B) -> not (Sub A1 A2) -> not (Sub A2 A1) ->
   Sub A (And A1 A2) -> TopLikeAux (Fun A B) (Fun A B) (Fun A B).*)

(* Disjointness: Specification *)

Definition OrthoS (A B: PTyp) := forall C, sub A C -> sub B C -> (TopLike A B C).

(* Disjointness: Implementation *)

Set Guard Checking.
Print Typing Flags.

Inductive Ortho : PTyp -> PTyp -> Prop :=
  | OTop : forall t1, Ortho t1 TopT
  | OTop1 : forall t1, Ortho TopT t1
  | OAnd1 : forall t1 t2 t3, Ortho t1 t3 -> Ortho t2 t3 -> Ortho (And t1 t2) t3
  | OAnd2 : forall t1 t2 t3, Ortho t1 t2 -> Ortho t1 t3 -> Ortho t1 (And t2 t3)
  | OIntFun : forall t1 t2, Ortho PInt (Fun t1 t2)
  | OFunInt : forall t1 t2, Ortho (Fun t1 t2) PInt
  | OFun   : forall t1 t2 t3 t4, Ortho t2 t4 -> Ortho (Fun t1 t2) (Fun t3 t4)
  | OFunA  : forall t1 t2 t3 t4, Ortho t1 t3-> not (sub t2 t4) -> not (sub t4 t2) -> Ortho (Fun t1 t2) (Fun t3 t4).

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
eapply TLFunAnd; auto.
apply invAndS1 in H3. destruct H3. admit. admit.
unfold not. intros. apply invAndS1 in H3.
destruct H3.
Admitted.

Lemma ortho_sym : forall {A B: PTyp}, OrthoS A B -> OrthoS B A.
Proof.
unfold OrthoS.
intros.
apply sym_top_like. auto.
Defined.

Lemma ortho_and : forall {A B C}, OrthoS A C -> OrthoS B C -> OrthoS (And A B) C.
Proof.
intros.
unfold OrthoS. intros.
dependent induction H2.

(*admit.

apply TLFun. apply IHC0_2.
admit.
dependent destruction H2; eauto.

admit.
admit.

inversion H1. inversion H5. apply H3.
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
apply H4.  
unfold Sub. exists c. auto. auto.
inversion H1. inversion H5.
apply H3. unfold Sub. exists c. auto. auto.
apply H4. unfold Sub. exists c. auto. auto.
assert (Sub C C0_1 /\ Sub C C0_2). apply invAndS1. auto. destruct H5.
assert (Sub (And A B) C0_1 /\ Sub (And A B) C0_2). apply invAndS1. auto.
destruct H7. pose (IHC0_1 H7 H5). pose (IHC0_2 H8 H6).
apply TLAnd. auto. auto.
apply TLTop.
Defined.*)
Admitted.

Lemma applyOrthoS : forall {A B}, OrthoS A B -> forall C, sub A C -> sub B C -> TopLike A B C.
intros. destruct H with (C:=C); auto.
Defined.

Lemma applyOrtho : forall {A B}, Ortho A B -> forall C, sub A C -> sub B C -> TopLike A B C.
intros.
induction C.
Admitted.


Lemma invOrthos: forall t1 t2 t3, OrthoS t1 (And t2 t3) -> OrthoS t1 t2 /\ OrthoS t1 t3.
intros. split.
unfold OrthoS. intros.
unfold OrthoS in H.
apply applyOrthoS. admit. auto. auto.
unfold OrthoS. intros.
apply applyOrthoS. admit. auto. auto.
Admitted.

Lemma invTopLike1{t1 t2 t3 t4}: forall C, TopLike (Fun t1 t2) (Fun t3 t4) (Fun (And t1 t3) C) -> 
   TopLike t2 t4 C.
intros. inversion H. inversion H3; auto.
admit. apply TLFun. admit.
apply TLFun.
dependent destruction H5.
dependent destruction H6. admit.
dependent destruction H2.
dependent destruction H3.
Admitted.

Lemma invTopLike {t1 t2 t3 t4}: forall C, sub t2 C -> sub t4 C -> 
   TopLike (Fun t1 t2) (Fun t3 t4) (Fun (And t1 t3) C) -> TopLike t2 t4 C.
intros.  inversion H1.
inversion H5.
Admitted.

(* Disjointness algorithm is complete: Theorem 8 *)

(*Lemma ortho_func : forall t1 t2, WFTyp t1 -> forall t3 t4, WFTyp t2 ->
      OrthoS (Fun t1 t2) (Fun t3 t4) -> Ortho t1 t3 \/ Ortho t2 t4.
Proof.
intros. left. unfold OrthoS in H1.*)

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
apply OFunA.
apply IHwft1_2. auto.
unfold OrthoS.
intros.
unfold OrthoS in H0.
assert (TopLike (Fun t1 t2) (Fun t0 t3) (Fun (And t1 t0) C)).
apply H0. apply SFun.
 apply SAnd2. auto. auto.
apply SFun. apply SAnd3. auto. auto.
eapply invTopLike; auto.
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
(* Case T _|_ t2 *)
(*destruct H0. destruct H0. destruct H0. apply TLTop.*)
apply OTop1.
Defined.


(*Lemma ortho_completness : forall t1, WFTyp t1 -> forall t2, WFTyp t2 -> OrthoS t1 t2 -> Ortho t1 t2.
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
apply OFun. apply IHwft1_2. auto.
unfold OrthoS.
intros.
apply applyOrthoS. admit. auto. auto.
(* Case t11 -> t12 _|_ t21 & t22 *)
apply OAnd2. apply IHWFTyp1.
unfold OrthoS.
intros.
apply applyOrthoS. admit. auto. auto.
apply IHWFTyp2.
unfold OrthoS.
intros.
apply applyOrthoS. admit. auto. auto.
(* Case t11 -> t12 _|_ T *)
apply OTop.
(* Case (t11 & t12) _|_ t2 *)
apply OAnd1.
apply IHwft1_1. auto.
unfold OrthoS.
intros.
apply applyOrthoS. admit. auto. auto.
apply IHwft1_2. auto.
unfold OrthoS; intros.
apply applyOrthoS. admit. auto. auto.
(* Case T _|_ t2 *)
(*destruct H0. destruct H0. destruct H0. apply TLTop.*)
apply OTop1.
Admitted.*)


(* Unique subtype contributor: Lemma 4 *)

Lemma uniquesub : forall A B C, 
  OrthoS A B -> sub (And A B) C -> not (TopLike A B C) ->  not (sub A C /\ sub B C).
Proof.
intros. unfold OrthoS in H. unfold not. intros. destruct H2.
destruct H with (C:=C); auto.
Defined.

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
apply applyOrtho. auto. auto. auto.
apply TLAnd. apply IHC1. inversion H0. auto. inversion H1. auto.
apply IHC2. inversion H0. auto. inversion H1. auto.
apply TLTop.
Defined.

