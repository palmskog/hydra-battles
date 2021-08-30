(**  

 Decidable, Total Pre-orders 

 Pierre Castéran, Univ. Bordeaux and LaBRI 
*)

From Coq Require Export Relations RelationClasses Setoid.
From Coq Require Import Program.Basics Bool.

Global Generalizable All Variables.

Class Decision (P : Prop) := decide : {P} + {~P}.
#[export] Hint Mode Decision ! : typeclass_instances.
Arguments decide _ {_} : simpl never, assert.

Class RelDecision {A B} (R : A -> B -> Prop) :=
  decide_rel x y :> Decision (R x y).
#[export] Hint Mode RelDecision ! ! ! : typeclass_instances.
Arguments decide_rel {_ _} _ {_} _ _ : simpl never, assert.
Notation EqDecision A := (RelDecision (@eq A)).

Class Total {A} (R : relation A) := total x y : R x y \/ R y x.

Definition flip_dec {A} (R : relation A) {rd : RelDecision R} :
  RelDecision (flip R) := fun x y => decide_rel R y x.
#[export] Hint Extern 3 (RelDecision (flip _)) => apply flip_dec : typeclass_instances.

Notation cast_if S := (if S then left _ else right _).
Notation cast_if_not S := (if S then right _ else left _).
Notation cast_if_and S1 S2 := (if S1 then cast_if S2 else right _).
Notation cast_if_or S1 S2 := (if S1 then left _ else cast_if S2).

Section prop_dec.

  Context {P} {Q} `(P_dec : Decision P) `(Q_dec : Decision Q).

  Global Instance not_dec: Decision (~P).
  Proof. refine (cast_if_not P_dec); intuition. Defined.

  Global Instance and_dec: Decision (P /\ Q).
  Proof. refine (cast_if_and P_dec Q_dec); intuition. Defined.

  Global Instance or_dec: Decision (P \/ Q).
  Proof. refine (cast_if_or P_dec Q_dec); intuition. Defined.

  Global Instance impl_dec: Decision (P -> Q).
  Proof. refine (if P_dec then cast_if Q_dec else left _); intuition. Defined.

End prop_dec.

Instance iff_dec {P} {Q} `(P_dec : Decision P) `(Q_dec : Decision Q) :
  Decision (P <-> Q) := and_dec _ _.

Instance Total_Reflexive {A} {R : relation A} `{!Total R} : Reflexive R.
Proof. intros a ; now destruct (total a a). Qed.

(** A class of total pre-orders *)

Class TotalPreOrder {A} (R : relation A) : Prop := {
  total_pre_order_pre :> PreOrder R;
  total_pre_order_total :> Total R
}.

Coercion Is_true : bool >-> Sortclass.
#[export] Hint Unfold Is_true : core.
#[export] Hint Immediate Is_true_eq_left : core.
#[export] Hint Resolve orb_prop_intro andb_prop_intro : core.

Lemma dec_stable {P:Prop} {dec: Decision P} : ~~P -> P.
Proof. firstorder. Qed.

Definition bool_decide (P : Prop) {dec : Decision P} : bool :=
  if dec then true else false.

Lemma bool_decide_reflect P {dec : Decision P} : reflect P (bool_decide P).
Proof. unfold bool_decide. destruct dec; [left|right]; assumption. Qed.

Lemma bool_decide_decide P {dec : Decision P} :
  bool_decide P = if decide P then true else false.
Proof. reflexivity. Qed.

Lemma decide_bool_decide P {Hdec: Decision P} {X : Type} (x1 x2 : X):
  (if decide P then x1 else x2) = (if bool_decide P then x1 else x2).
Proof. unfold bool_decide, decide. destruct Hdec; reflexivity. Qed.

Tactic Notation "destruct_decide" constr(dec) "as" ident(H) :=
  destruct dec as [H|H];
  try match type of H with
  | ~~_ => apply dec_stable in H
  end.
Tactic Notation "destruct_decide" constr(dec) :=
  let H := fresh in destruct_decide dec as H.

Tactic Notation "case_bool_decide" "as" ident (Hd) :=
  match goal with
  | H : context [@bool_decide ?P ?dec] |- _ =>
    destruct_decide (@bool_decide_reflect P dec) as Hd
  | |- context [@bool_decide ?P ?dec] =>
    destruct_decide (@bool_decide_reflect P dec) as Hd
  end.

Tactic Notation "case_bool_decide" :=
  let H := fresh in case_bool_decide as H.

Lemma bool_decide_eq_true (P : Prop) `{Decision P} : bool_decide P = true <-> P.
Proof. case_bool_decide; intuition discriminate. Qed.

Lemma bool_decide_eq_false (P : Prop) `{Decision P} : bool_decide P = false <-> ~P.
Proof. case_bool_decide; intuition discriminate. Qed.

Lemma bool_decide_iff (P Q : Prop) `{Decision P, Decision Q} :
  (P <-> Q) -> bool_decide P = bool_decide Q.
Proof. repeat case_bool_decide; tauto. Qed.

(** when applied to a pre-order relation le, returns the equivalence and
    the strict order associated to le *)

Definition preorder_equiv {A} {le : relation A} {P : PreOrder le} (a b : A) :=
 le a b /\ le b a.

Definition lt {A} {le : relation A} {P: PreOrder le} (a b : A) :=
 le a b /\ ~ le b a.

(** Properties of decidable total pre-orders *)
Lemma lt_irreflexive {A} {le : relation A} {P : PreOrder le} :
  forall a, ~ lt a a.
Proof.
 destruct 1; contradiction. 
Qed.

Lemma lt_not_ge {A} {le:relation A} {P : PreOrder le} :
 forall a b, lt a b -> ~ le b a.
Proof.
 intros a b [H H0]; assumption.
Qed.

Lemma not_le_ge {A} {le:relation A} {P0 : TotalPreOrder le} :
  forall a b, ~ le a b -> le b a.
Proof.
  intros a b H. destruct P0.
  destruct (total a b).
  - contradiction.
  - assumption.
Qed.

Lemma le_not_gt {A} {le:relation A} {P:PreOrder le} :
  forall a b,  le a b -> ~ lt b a.
Proof.
  intros a b H H0;  now destruct (lt_not_ge b a).
Qed.

Lemma lt_not_equiv {A} {le:relation A} {P:PreOrder le} :
  forall a b, lt a b -> ~ preorder_equiv a b.
Proof.
 intros a b H H0; destruct H, H0; contradiction.
Qed.  

Lemma equiv_not_lt {A} {le:relation A} {P:PreOrder le} :
  forall a b, preorder_equiv a b -> ~ lt a b.
Proof.
 intros a b H H0; destruct H, H0; contradiction.
Qed.

Lemma lt_le_trans {A} {le:relation A} {P:PreOrder le} :
 forall a b c, lt a b -> le b c -> lt a c.
Proof.
  intros a b c [Hab H'ab]  Hbc;  split.
  - now transitivity b.
  - intro H; destruct H'ab; now transitivity c.
Qed.

Lemma le_lt_trans {A} {le:relation A} {P:PreOrder le} :
 forall a b c, le a b -> lt b c -> lt a c.
Proof.
  intros a b c Hab [Hbc H'bc];  split.
  - now transitivity b.
  - intro H; destruct H'bc; now transitivity a.
Qed.

Lemma le_lt_weak {A} {le:relation A} {P:PreOrder le} :
 forall a b, lt a b -> le a b.
Proof. now destruct 1. Qed.

Instance lt_transitive {A} {le:relation A} {P:PreOrder le} :
 Transitive lt.
Proof.
 intros x y z [Hxy H'xy] [Hyz H'yz];  split.
 - now transitivity y.
 - intro H; destruct H'yz; now transitivity x.
Qed.

Instance equiv_equiv {A} {le:relation A} {P: PreOrder le} :
 Equivalence preorder_equiv.
Proof.
split.
- intro x;split;reflexivity.
- intros x y Hxy;destruct Hxy;split;auto.
- intros x y z Hxy Hyz; destruct Hxy, Hyz; split; transitivity y;auto.
Qed.

Definition le_lt_equiv_dec {A} {le : relation A}
 {P0 : TotalPreOrder le} {dec : RelDecision le} (a b : A) :
 le a b -> {lt a b}+{preorder_equiv a b}.
Proof.
  intro H; destruct (decide (le b a)).
  - right;split;auto.
  - left;split;auto.
Defined.

Lemma not_le_gt {A} (le : relation A) {P0: TotalPreOrder le} (a b : A) :
 ~ le a b -> lt b a.
Proof.
  intro H. destruct (total b a).
  - split; auto.   
  - contradiction.
Qed.
