Require Import RelationClasses Relation_Operators Ensembles.
Import Relation_Definitions.

Require Export MoreOrders.

Generalizable All Variables.

(**
  Ordinal notation system on type [A] :

*)

Class OrdinalNotation {A:Type}(lt: relation A)
      (compare : A -> A -> comparison)  :=
  {
  sto :> StrictOrder lt;
wf :> well_founded lt;
  compare_correct :
    forall alpha beta:A,
      CompareSpec (alpha=beta) (lt alpha beta) (lt beta alpha)
                  (compare alpha beta);
  }.

Definition comp {A:Type}{lt: relation A}
            {compare : A -> A -> comparison}
            {on : OrdinalNotation lt compare} := compare.


 Definition ZeroLimitSucc_dec {A:Type}{lt: relation A}
            {compare : A -> A -> comparison}
            {on : OrdinalNotation lt compare} :=
            
    forall alpha,
      {Least alpha}+
      {Limit alpha} +
      {beta: A | Successor alpha beta}.

 About ZeroLimitSucc_dec.

(** The segment called [O alpha] in Schutte *)

Definition bigO `{nA : @OrdinalNotation A ltA compareA}
           (a: A) : Ensemble A :=
  fun x: A => ltA x a.


(** The segment associated with nA is isomorphic to
    the interval [0,b[ *)

Class  SubSegment 
       `(nA : @OrdinalNotation A ltA  compareA)
       `(nB : @OrdinalNotation B ltB  compareB)
       (b :  B)
       (iota : A -> B):=
  {
  subseg_compare :forall x y : A,  compareB (iota x) (iota y) =
                                 compareA x y;
  subseg_incl : forall x, ltB (iota x) b;
  subseg_onto : forall y, ltB y b  -> exists x:A, iota x = y}.


Class  Isomorphic 
       `(nA : @OrdinalNotation A ltA compareA)
       `(nB : @OrdinalNotation B ltB  compareB)
       (f : A -> B)
       (g : B -> A):=
  {
  iso_compare_comm :forall x y : A,  compareB (f x) (f y) =
                                 compareA x y;
  iso_inv1 : forall a, g (f a)= a;
  iso_inv2 : forall b, f (g b) = b}.

  
  

 
