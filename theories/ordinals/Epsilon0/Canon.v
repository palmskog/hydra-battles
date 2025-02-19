
(**  Canonical Sequences of ordinals below epsilon0

Pierre Casteran, 
       LaBRI and University of Bordeaux.

       After J. Ketonen and R. Solovay's paper
  " Rapidly Growing Ramsey Functions" _in_
    Annals of mathematics, Mar. 1981 

 *)

From Coq Require Export Arith Lia.
Import Relations Relation_Operators.

From hydras.Epsilon0 Require Export T1 E0.

Set Implicit Arguments.
Open Scope t1_scope.

(** * Definitions *)

(* begin snippet canonDef *)

Fixpoint canon alpha (i:nat) : T1 :=
  match alpha with
    zero => zero
  | ocons zero 0 zero  => zero
  | ocons zero (S k) zero  => FS k
  | ocons gamma 0 zero => (match T1.pred gamma with
                            Some gamma' =>
                            match i with 0 => zero
                                    |   S j => ocons gamma' j zero
                            end
                          | None =>
                            ocons (canon gamma i) 0 zero
                           end)
  
  |  ocons gamma (S n) zero =>
     (match T1.pred gamma with
       Some gamma' =>
       (match i with
         0 =>  ocons gamma n zero
       | S j => ocons gamma n (ocons gamma' j zero)
       end)
      | None => ocons gamma n (ocons (canon gamma  i) 0 zero)
      end)
   |  ocons alpha n beta => ocons alpha n (canon beta i)  
end.
(* end snippet canonDef *)

(* begin snippet canonExamples *)

Section Canon_examples.
Import T1. 

Compute pp (canon (omega ^ omega) 3).

Compute pp (canon (omega ^ omega * 3) 42).

Compute canon (phi0 10) 0.

Goal canon (omega ^ omega) 10 = phi0 10. (* .no-out *)
Proof. (* .no-out *) reflexivity. Qed. 

End Canon_examples.
(* end snippet canonExamples *)

(* compatibility with older versions *)

(* begin snippet canonS0 *)

Definition  canonS alpha (i:nat) : T1 :=
  canon alpha (S i).

Definition  canon0 alpha  : T1 :=
  canon alpha 0.

(* end snippet canonS0 *)

(** * Properties of canonical sequences *)

Lemma canon_zero i :  canon zero i = zero.
Proof. reflexivity.  Qed.

Lemma canon_tail :
  forall alpha n beta i,  nf (ocons alpha n beta) -> 
                          beta <> 0 ->
                          canon (ocons alpha n beta) i =
                          ocons alpha n (canon beta i).
Proof.
  destruct alpha as [| alpha1 n alpha2].
  - destruct 2; auto.
    eapply nf_of_finite; eauto.
  - intros; simpl;  destruct n0, beta; auto.
    + destruct H0; auto. 
    + destruct H0; auto.
Qed.


Lemma canonS_lim1 : forall i lambda, nf lambda -> limitb lambda 
                                 -> canon (ocons lambda 0 zero) (S i) =
                                    T1.phi0 (canon lambda (S i)).
Proof.
  intros; unfold canon at 1;  destruct lambda.
  -  discriminate.
  -  replace ( T1.pred (ocons lambda1 n lambda2)) with (@None T1).
     + f_equal. 
     + rewrite pred_of_limit;auto.
Qed.

Lemma canon_lim1 : forall i lambda, nf lambda -> limitb lambda 
                                    -> canon (ocons lambda 0 zero)  i =
                                       T1.phi0 (canon lambda i).
Proof.
  destruct i. 
  - intros; unfold canon at 1;  destruct lambda.
    +   discriminate.
    +   replace ( T1.pred (ocons lambda1 n lambda2)) with (@None T1).
        * f_equal. 
        * rewrite pred_of_limit;auto.
  - intros; apply canonS_lim1; auto. 
Qed.

(** Here *)

Lemma canonS_lim2  i n lambda: 
    nf lambda -> limitb lambda 
    -> canon (ocons lambda (S n) zero) (S i) =
       ocons  lambda n (T1.phi0 (canon lambda (S i))).
Proof.
  intros;  cbn;  destruct lambda.
  - simpl; discriminate.
  - remember (ocons lambda1 n0 lambda2) as lambda.
    replace (pred lambda) with (@None T1).
    + trivial.
    + now rewrite pred_of_limit.
Qed.

Lemma canon0_lim2   n lambda: 
    nf lambda -> limitb lambda 
    -> canon (ocons lambda (S n) zero) 0 =
       ocons  lambda n (T1.phi0 (canon lambda 0)).
Proof.
  intros;  cbn; destruct lambda.
  - simpl; discriminate.
  -  replace ( T1.pred (ocons lambda1 n0 lambda2)) with (@None T1);   f_equal.
  rewrite T1.pred_of_limit;auto.
Qed.

Lemma canon_lim2  i  n lambda : 
    nf lambda -> limitb lambda 
    -> canon (ocons lambda (S n) zero) i =
       ocons  lambda n (T1.phi0 (canon lambda i)).
Proof.
 destruct i; intros.
 - now  apply canon0_lim2.
 - now apply canonS_lim2.
Qed.

(* begin snippet canonSucc *)

Lemma canon_succ i alpha :
  nf alpha -> canon (succ alpha) i = alpha. (* .no-out *)
Proof. (* .no-out *)
  revert i; induction alpha.
  (* ... *)
  (*| .. coq:: none |*)
  - reflexivity.
  - destruct alpha1.
      + intros; replace alpha2 with zero.   
        * reflexivity. 
        *  T1_inversion H; auto. 
      +  intros; simpl;  destruct n.
         * destruct alpha2.
          { reflexivity. }
          { simpl;destruct alpha2_1.
            - f_equal;  apply nf_inv2 in H.
              T1_inversion H; now subst. 
            - f_equal. rewrite <- IHalpha2 with i; f_equal. eapply nf_inv2, H. }
         *  case_eq (T1.succ alpha2).
            { intros;  now destruct (@T1.succ_not_zero alpha2). }
            { intros; f_equal ; rewrite <- IHalpha2 with i.
              - now rewrite <- H0.
              - eapply nf_inv2, H. }
(*||*)
Qed.
(* end snippet canonSucc *)

(** should be deprecated later *)
Lemma canonS_succ i alpha : nf alpha -> canonS (succ alpha) i = alpha.
Proof.
   intros; now apply canon_succ.
Qed.

Lemma canon0_succ  alpha : nf alpha -> canon0 (succ alpha)  = alpha.
Proof.
  intros; now apply canon_succ.
Qed.


Lemma canonS_phi0_succ_eqn i gamma:
  nf gamma -> 
  canon (T1.phi0 (succ gamma)) (S i) = ocons gamma i zero.
Proof.
  intros;  cbn. rewrite T1.pred_of_succ;
    case_eq (T1.succ gamma); trivial.
  -  intro; destruct (succ_not_zero _ H0); auto 2.
Qed.





Lemma canon0_phi0_succ_eqn  gamma:
  nf gamma -> 
  canon  (T1.phi0 (succ gamma)) 0 = zero.
Proof.
  intros;   cbn; rewrite T1.pred_of_succ; auto.
    case_eq (T1.succ gamma); trivial.
Qed.


Lemma canonS_ocons_succ_eqn2 i n gamma :
    nf gamma -> 
    canon (ocons (T1.succ gamma) (S n) zero) (S i) =
    ocons (T1.succ gamma) n (ocons gamma i zero).
Proof.
  intros;  cbn;  rewrite T1.pred_of_succ;
    case_eq (T1.succ gamma); trivial.
  -  intro; destruct (T1.succ_not_zero _ H0).
Qed.


Lemma canon0_ocons_succ_eqn2 n gamma :
    nf gamma -> 
    canon (ocons (T1.succ gamma) (S n) zero)  0=
    ocons (T1.succ gamma) n zero.
Proof.
  intros; cbn;  rewrite T1.pred_of_succ;
    case_eq (T1.succ gamma); trivial.
Qed.

Lemma canonSSn (i:nat) :
  forall alpha n  ,
    nf alpha -> 
    canon (ocons alpha (S n) zero) i =
    ocons alpha n (canon (ocons alpha 0 zero) i).
Proof. 
  intros; destruct (@zero_limit_succ_dec alpha); trivial.
  - destruct s.
    + destruct n; subst alpha;  reflexivity.       
    + rewrite canon_lim2 ; auto.
      rewrite canon_lim1; auto.
  - destruct s as [beta [Hdeta e]]; subst alpha.
    destruct i.
       rewrite canon0_ocons_succ_eqn2, canon0_phi0_succ_eqn; auto.
           rewrite canonS_ocons_succ_eqn2 , canonS_phi0_succ_eqn; auto.   
Qed.


Lemma canonS_zero_inv (alpha:T1) (i:nat) : 
  canon alpha (S i) = zero -> alpha = zero \/ alpha = one.
Proof.
  destruct alpha; cbn; auto.
  destruct alpha1, n, alpha2;auto; try discriminate.
  all:  destruct (T1.pred (ocons alpha1_1 n0 alpha1_2)); try discriminate.
Qed.


(** ** Canonical sequences and the order LT *)

(* begin snippet canonSLT *)

(*| .. coq:: no-out |*)
Lemma canonS_LT i alpha :
  nf alpha -> alpha <> zero ->
  canon alpha (S i) t1<  alpha.
Proof.
  transfinite_induction_lt alpha.
  (* ... *)  (*||*)  (*| .. coq:: none |*)
  clear alpha; intros alpha Hrec Halpha;
    destruct (zero_limit_succ_dec Halpha).
    - destruct s.
      + (* alpha = zero *)
       subst alpha; now destruct 1.
      + (* alpha is a limit *)
        destruct alpha.
        * now destruct 1.
        * intros H; destruct (T1_eq_dec alpha1 zero).
          { subst.
            destruct n.
            - replace alpha2 with zero.
              + split;auto. 
                simpl;  constructor.
                split;simpl;constructor.
              + T1_inversion Halpha; auto.
            -  replace alpha2 with zero.
               +  simpl; split;  constructor.
                  apply finite_lt; auto with arith. 
                  apply nf_FS.
               +  T1_inversion Halpha; auto. 
          }
          destruct alpha2.
          { destruct n.
             {   destruct  (@zero_limit_succ_dec alpha1) ; trivial. 
                 - destruct s.
                  + subst;  now destruct n0. 
                  + rewrite canonS_lim1.
                    * split.
                      --   apply single_nf; auto.
                 destruct (Hrec alpha1) ; trivial. 
                 apply head_lt_ocons ;  auto.
                 -- split; auto with T1.
                  ++   apply head_lt; apply Hrec ; trivial.
                       apply head_lt_ocons; auto.
                    * auto with T1.
                    * trivial.
                 -  destruct s.
                 { destruct a.
                     { subst; rewrite canonS_phi0_succ_eqn.
                       - split.
                       + apply single_nf; auto. 
                       + split; trivial.
                         * apply head_lt; auto.
                           apply lt_succ; auto. 
                       - assumption.
                     }
                 }
             }
             destruct  (@zero_limit_succ_dec alpha1) ; trivial.
             { destruct s.
               - subst; now destruct n0.   
               - rewrite canonS_lim2.
                 + split.
                  { apply ocons_nf ; trivial.
                    - destruct (Hrec alpha1) ; eauto with T1.
                      + apply head_lt_ocons.
                      + tauto.
                    -  apply single_nf. 
                      destruct (Hrec alpha1); trivial. 
                      apply head_lt_ocons.
                  }
                  split.
                   * apply coeff_lt; auto with arith.
                   * auto with T1.
                     + eapply nf_inv1, Halpha.  
                     + auto.
             }
             destruct s; subst.
             {  destruct a; subst; rewrite canonS_ocons_succ_eqn2.
                  -  split.
                   { apply ocons_nf. 
                     - apply lt_succ.
                     - apply succ_nf; auto.
                     - apply single_nf; auto.
                   }
                     + split.
                       {  apply coeff_lt; auto with arith. }
                       auto with T1.
                  - auto.
             }
          }
          rewrite canon_tail.
          {
            split.
            {
              nf_decomp Halpha.
              apply nf_intro ; trivial.
              - destruct (Hrec  (ocons alpha2_1 n1 alpha2_2)) ; trivial.
               now apply head_lt.
                discriminate.
              - apply nf_helper_phi0R.
                apply T1.lt_trans with (ocons alpha2_1 n1 alpha2_2).
                + destruct (Hrec (ocons alpha2_1 n1 alpha2_2)) ; trivial.
                  apply head_lt; auto. 
                  *  discriminate.
                  * tauto.
             +  
                apply nf_helper_phi0.
                apply nf_helper_intro with n;auto.
            }
            split.
          
            - nf_decomp Halpha.
              apply tail_lt. 
              destruct (Hrec (ocons alpha2_1 n1 alpha2_2)); auto.
              +  auto with T1.
            + discriminate. 
            + destruct (Hrec (ocons alpha2_1 n1 alpha2_2)) ; trivial.
              eauto with T1.
              discriminate.
              tauto. 
            - trivial. 
          }
           eauto with T1.
          discriminate.
    - destruct s.
      {   destruct a; subst.
          intros.  rewrite canon_succ; auto.
          split; auto.
          split; auto; apply lt_succ; auto.
      }
      (*||*)
Qed. 
(* end snippet canonSLT *)

Lemma canon0_LT  alpha :
  nf alpha -> alpha <> zero ->
  canon alpha 0 t1<  alpha.
Proof.
  transfinite_induction_lt alpha.
  clear alpha; intros alpha Hrec Halpha;
    destruct (zero_limit_succ_dec Halpha).
    - destruct s.
      + (* alpha = zero *)
       subst alpha; now destruct 1.
      + (* alpha is a limit *)
        destruct alpha.
        * now destruct 1.
        * intros H; destruct (T1_eq_dec alpha1 zero).
          { subst.
            destruct n.
            - replace alpha2 with zero.
              + split;auto. 
                simpl;  constructor.
                split;simpl;constructor.
              + T1_inversion Halpha; auto.
            -  replace alpha2 with zero.
               +  simpl; split;  constructor.
                  apply finite_lt; auto with arith. 
                  apply nf_FS.
               +  T1_inversion Halpha; auto. 
          }
          destruct alpha2.
          { destruct n.
             {   destruct  (@zero_limit_succ_dec alpha1) ; trivial. 
                 - destruct s.
                  + subst;  now destruct n0. 
                  + rewrite canon_lim1.
                    * split.
                      --   apply single_nf; auto.
                 destruct (Hrec alpha1) ; trivial. 
                 apply head_lt_ocons ;  auto.
                 -- split; auto with T1.
                  ++   apply head_lt; apply Hrec ; trivial.
                       apply head_lt_ocons; auto.
                    * auto with T1.
                    * trivial.
                 -  destruct s.
                 { destruct a.
                     { subst; rewrite canon0_phi0_succ_eqn.
                       - split.
                       + auto with T1.
                       + split; trivial.
                         *  auto with T1.
                       - assumption.
                     }
                 }
             }
             destruct  (@zero_limit_succ_dec alpha1) ; trivial.
             { destruct s.
               - subst; now destruct n0.   
               - rewrite canon0_lim2.
                 + split.
                  { apply ocons_nf ; trivial.
                    - destruct (Hrec alpha1) ; eauto with T1.
                      + apply head_lt_ocons.
                      + tauto.
                    -  apply single_nf. 
                      destruct (Hrec alpha1); trivial. 
                      apply head_lt_ocons.
                  }
                  split.
                   * apply coeff_lt; auto with arith.
                   * auto with T1.
                     + eapply nf_inv1, Halpha.  
                     + auto.
             }
             destruct s; subst.
             {  destruct a; subst; rewrite canon0_ocons_succ_eqn2.
                  -  split.
                   { eauto with T1. 
                   }
                     + split.
                       {  apply coeff_lt; auto with arith. }
                       auto with T1.
                  - auto.
             }
          }
          rewrite canon_tail.
          {
            split.
            {
              nf_decomp Halpha.
              apply nf_intro ; trivial.
              - destruct (Hrec  (ocons alpha2_1 n1 alpha2_2)) ; trivial.
               now apply head_lt.
                discriminate.
              - apply nf_helper_phi0R.
                apply T1.lt_trans with (ocons alpha2_1 n1 alpha2_2).
                + destruct (Hrec (ocons alpha2_1 n1 alpha2_2)) ; trivial.
                  apply head_lt; auto. 
                  *  discriminate.
                  * tauto.
             +  
                apply nf_helper_phi0.
                apply nf_helper_intro with n;auto.
            }
            split.
          
            - nf_decomp Halpha.
              apply tail_lt. 
              destruct (Hrec (ocons alpha2_1 n1 alpha2_2)); auto.
              +  auto with T1.
            + discriminate. 
            + destruct (Hrec (ocons alpha2_1 n1 alpha2_2)) ; trivial.
              eauto with T1.
              discriminate.
              tauto. 
            - trivial. 
          }
           eauto with T1.
          discriminate.
    - destruct s.
      {   destruct a; subst.
          intros; rewrite canon_succ; auto.
          split; auto.
          split; auto; apply lt_succ; auto.
      }
Qed. 


Lemma nf_canon  i alpha:  nf alpha -> nf (canon alpha i).
Proof.
  intros Hnf; destruct (T1_eq_dec alpha zero).
  - subst; constructor.
  - destruct i.
    destruct  (canon0_LT   Hnf); auto.
    destruct  (canonS_LT  i  Hnf); auto.
Qed.



Lemma canonS_lt : forall i alpha, nf alpha -> alpha <> zero ->
                              T1.lt (canon alpha (S i)) alpha.
Proof.
  intros i alpha Hnf.
  destruct (T1_eq_dec alpha zero).
  - subst. now destruct 1.
  - destruct  (canonS_LT i Hnf); tauto.
Qed.

Lemma canonS_cons_not_zero : forall i alpha n beta,
    alpha <> zero -> canon (ocons alpha n beta) (S i) <> zero.
Proof. 
  destruct alpha.
  -  now destruct 1.
  -  intros; cbn.
     destruct n0, beta, alpha1, n; try discriminate. 
     all: destruct (T1.pred alpha2); try discriminate. 
Qed.



(** ** Canonical sequences of limit ordinals *)


Lemma limitb_canonS_not_zero i lambda:
  nf lambda -> limitb lambda  -> canon lambda (S i) <> zero.
Proof.
  destruct lambda as [ | alpha1 n alpha2].
  - discriminate.
  - intros; simpl; destruct alpha1.
    +   destruct n.
        *  destruct alpha2 ; discriminate.
        *  destruct alpha2; discriminate.
    +  destruct n.
       *  destruct alpha2.
          {  destruct (T1.pred (ocons alpha1_1 n0 alpha1_2));
               discriminate. }
          discriminate.
       *   destruct alpha2.
           destruct (T1.pred (ocons alpha1_1 n0 alpha1_2));
             discriminate.
           discriminate.
Qed.

(** 
Let lambda  be a limit ordinal. For any beta < lambda, we can 
compute some item of the canonical sequence  of lambda which is 
greater than beta.
   
   It is a constructive way of expressing that lambda is the 
limit of its  own canonical sequence 
*)

(* begin snippet canonSLimitStrong *)

(*| .. coq:: no-out *)
Lemma canonS_limit_strong lambda : 
  nf lambda ->
  limitb lambda  ->
  forall beta, beta t1< lambda ->
               {i:nat | beta t1< canon lambda (S i)}.
Proof.
  transfinite_induction lambda.
  (* ... *) (*||*) (*| .. coq:: none |*)
  clear lambda ; intros lambda Hrec Hlambda.
  intros   H beta H1.
  assert (Hbeta: nf beta)  by eauto with T1.
  destruct (zero_limit_succ_dec Hlambda).
  -   destruct s.   
      { (* lambda = zero *)
        subst lambda; inversion H1;  destruct (not_LT_zero H1).
      }
      destruct lambda.
      + discriminate.
      + destruct (T1.limitb_cases Hlambda i).
       { (* first case : beta = zero *)
        destruct a; subst lambda2; destruct beta.
        { exists 0; apply not_zero_lt. 
          apply nf_canon; auto.
          apply limitb_canonS_not_zero;auto.
        }
        destruct (LT_inv_strong H1).
        * destruct n.
          destruct (@zero_limit_succ_dec   lambda1); trivial. 
        -- destruct s.
           ++ subst; assert (False) by (eapply not_LT_zero; eauto).
              contradiction. 
           ++ assert {i :nat | (beta1 t1< canonS lambda1 i)%t1}.         
              { apply Hrec.
                apply head_LT_cons; auto with T1.
                all: auto.
              }
              destruct H3 as [x l].
              exists x; rewrite canonS_lim1; trivial; eauto with T1.
        --  destruct s as [x [H4 H5]].
            subst lambda1; assert ({beta1 t1< x} + {beta1 = x})%t1.
            { apply  LT_succ_LT_eq_dec in H2; trivial. eapply nf_inv1, Hbeta. }
            destruct H3.
            ++ exists 0; rewrite canonS_phi0_succ_eqn;auto with T1.
            ++ subst; exists (S n0);  rewrite canonS_phi0_succ_eqn; auto. 
               apply LT3; auto with arith.
        -- clear i; exists 0; rewrite canonSSn.
           ++ apply LT2; trivial.
              apply nf_intro; trivial.
              now apply nf_canon.
              apply nf_helper_phi0R.
              apply canonS_lt.
              eapply nf_coeff_irrelevance;eauto. 
              discriminate. 
           ++ eapply nf_inv1, Hlambda. 
        *  subst.
           -- destruct n.
              abstract lia.
              apply lt_n_Sm_le in H3.
              destruct (Compare_dec.le_lt_eq_dec _ _ H3).
              exists 0; rewrite canonSSn. 
             apply LT3; auto.
             {
               apply nf_intro; trivial.
               apply nf_canon; trivial.
               apply nf_helper_phi0R.
               apply canonS_lt.
               eapply nf_coeff_irrelevance;eauto.     
               discriminate.  
             }
             { eapply nf_inv1, Hlambda. }
             
             assert {i: nat |  beta2 t1< (canonS (ocons lambda1 0 zero) i)}%t1.
             { apply Hrec.
               -- apply LT3;auto with arith.
               -- cbn;  destruct lambda1.
                  destruct H1; auto.
                  auto.
               -- cbn; destruct lambda1.
                  cbn in H; discriminate.
                  auto. 
               --  split.
                   ++ eapply nf_inv2, Hbeta.
                   ++ split. 
                      ** apply nf_helper_phi0.     
                      apply nf_helper_intro with n0;auto with T1.
                      ** eapply nf_coeff_irrelevance;eauto.     
             }
             subst;
               assert
                 ({i: nat |  beta2 t1< (canonS (ocons lambda1 0 zero) i)})%t1.
             { apply Hrec.
               - apply LT3;auto with arith.
               - cbn;  destruct lambda1.
               + destruct H2;auto. 
               + auto.
               - cbn;  destruct lambda1.
                 + destruct H2; auto. 
                 + auto.                
               - split.
                 + eapply nf_inv2, Hbeta. 
                 + split. 
                 * apply nf_helper_phi0.    
                  apply nf_helper_intro with n;auto with T1.
                 * eapply nf_coeff_irrelevance;eauto.   
             }
             destruct H4;  exists x; rewrite canonSSn. 
             apply LT4;auto.
             { 
               apply nf_intro; auto with T1.
               eauto with T1.
               apply nf_helper_phi0R.   
               apply canonS_lt.
               now apply nf_phi0. 
               intro; subst; discriminate.
             }
             auto.
        *  elimtype False.
           destruct (not_LT_zero H4).
      }
      destruct a ;  assert (lambda2 <> zero). {
        intro; subst; discriminate.  } 
      destruct beta.
       * exists 0;  apply not_zero_lt.
         apply nf_canon; trivial; auto with T1.
         apply limitb_canonS_not_zero; trivial. 
       *  destruct (LT_inv_strong H1).
          -- exists 0;  rewrite canon_tail.
             apply LT2;auto.
             { apply nf_intro;  trivial.
               eauto with T1.
            apply nf_canon; trivial; eauto with T1.
            apply nf_helper_phi0R.   
            apply T1.lt_trans with lambda2.
            apply canonS_lt; eauto with T1.
            apply nf_helper_phi0.
            apply nf_helper_intro with n; eauto with T1.
          }
          auto.
          auto.
         --  destruct H4; exists 0; rewrite canon_tail.
             apply LT3;  auto.
             { apply nf_intro. 
               - eauto with T1.
               - apply nf_canon; eauto with T1.
               - apply nf_helper_phi0R.   
                 apply T1.lt_trans with lambda2.
                 apply canonS_lt; eauto with T1.
                 apply nf_helper_phi0.
                 apply nf_helper_intro with n; eauto with T1.
             }
             all: auto. 
      --  subst; assert ({i: nat |  beta2 t1< (canonS lambda2 i)})%t1.
      { apply Hrec.
        { apply tail_LT_cons; auto. }
        1,2: eauto with T1.
        assumption.
      }
      destruct H4 as [x Hx]; exists x; rewrite canon_tail.
      apply LT4; auto. 
      {
        apply nf_intro. 
        eauto with T1.
        apply nf_canon; eauto with T1.
        apply nf_helper_phi0R.   
        apply T1.lt_trans with lambda2.
        apply canonS_lt; eauto with T1.
        apply nf_helper_phi0.
        apply nf_helper_intro with n; eauto with T1.
      }
      all: auto. 
  -   destruct s as [t [Ht Ht']]; subst lambda.
      destruct (@limitb_succ t); auto.
      (*||*)
Defined.
      (* end snippet canonSLimitStrong *)

Lemma canon_limit_strong lambda : 
  nf lambda ->
  limitb lambda  ->
  forall beta, beta t1< lambda ->
                {i:nat | beta t1< canon lambda i}.
Proof.
  intros H H0 beta H1; destruct (canonS_limit_strong H H0 H1) as [x Hx];
    exists (S x);auto.
Defined.

(* begin snippet canonSLimitLub *)

Lemma canonS_limit_lub (lambda : T1) :
  nf lambda -> limitb lambda  ->
  strict_lub (canonS lambda) lambda. (* .no-out *) (*| .. coq:: none |*)
Proof.
  split.
  - intros; split.
    + now  apply nf_canon.
    +    split; trivial.
         * apply canonS_lt;    auto.
           intro H1;subst; discriminate.
  - intros l' Hl';  assert (nf l').
    {  specialize (Hl' 0). eauto with T1. }
    destruct (T1.lt_eq_lt_dec lambda l').
    + repeat split;auto.
      destruct s.
      *  now left.
      *  subst; now right.
    + assert (l' t1< lambda)%t1 by (split; auto).
      destruct (canonS_limit_strong H H0 H2).
      specialize (Hl' x).
      assert (l' t1< l')%t1.
      { apply LT_LE_trans with  (canonS lambda x); auto. }
      now destruct (@LT_irrefl l' ).
Qed. 
(*||*)
(* end snippet canonSLimitLub *)


Lemma canonS_limit_mono alpha i j : nf alpha -> limitb alpha  ->
                                    i < j ->
                                    canonS alpha i t1< canonS alpha j.
Proof. 
  pattern alpha ; apply transfinite_recursor_lt.
  clear alpha;  intros alpha Hrec alpha_nf.
  intros.  
  destruct alpha.
  - discriminate.
  -  nf_decomp alpha_nf.
     destruct (limitb_cases alpha_nf H).
     +  destruct a;subst.
        destruct (@zero_limit_succ_dec alpha1) ; trivial.
        *   destruct s.   
            { subst;   discriminate H. }
            {   destruct n.
                - unfold canonS; repeat rewrite canonS_lim1 ; trivial.
                  {  apply LT2 ; trivial.
                     apply single_nf. 
                     apply nf_canon ; eauto with T1.
                     apply single_nf. 
                     apply nf_canon ; eauto with T1.
                     apply Hrec ; trivial. 
                     apply head_lt_ocons.
                  }
                - unfold canonS; repeat rewrite canonS_lim2 ; trivial. 
                  {
                    apply LT4 ; trivial.
                    apply nf_ocons_LT ; trivial.
                    apply canonS_LT ; trivial.
                    apply single_nf. 
                    apply nf_canon ; trivial.
                    apply nf_ocons_LT; trivial.
                    apply canonS_LT ; eauto with T1.
                    apply single_nf; apply nf_canon ; eauto with T1.
                    apply LT2 ; trivial.
                    apply single_nf;
                      apply nf_canon ; eauto with T1.
                    apply single_nf;
                      apply nf_canon ; eauto with T1.
                    apply Hrec ; trivial.
                    apply head_lt_ocons.
                  }
            }
        * destruct s;subst.
          destruct a.
          subst alpha1.
          destruct n.
          { unfold canonS; repeat rewrite canonS_phi0_succ_eqn ;
              eauto with T1. }
          {
            unfold canonS; repeat rewrite canonS_ocons_succ_eqn2 ; trivial. 
            apply LT4 ; trivial.
            apply nf_ocons_LT ; eauto with T1.
            apply LT_succ ; eauto with T1.
            apply nf_ocons_LT ; eauto with T1.
            apply LT_succ ; eauto with T1.
            auto with T1.
          }
     + destruct a. unfold canonS;
       repeat rewrite canon_tail ; eauto with T1.
       nf_decomp alpha_nf.
       * apply  LT4 ; trivial.
         apply nf_intro ; trivial. 
         apply nf_canon ; eauto with T1.
         apply nf_helper_phi0R ; trivial. 
         apply T1.lt_trans with alpha2 ; trivial. 
         apply canonS_lt ; eauto with T1.
         apply nf_helper_phi0 ; eauto with T1.
         apply nf_helper_intro with n ; eauto with T1.
         apply nf_intro ; trivial. 
         apply nf_canon ; eauto with T1.
         apply nf_helper_phi0R ; trivial. 
         apply T1.lt_trans with alpha2; trivial. 
         apply canonS_lt ; eauto with T1.
         apply nf_helper_phi0 ; eauto with T1.
         apply nf_helper_intro with n ; eauto with T1.
         apply Hrec ; eauto with T1.
         apply tail_lt_ocons ; eauto with T1.
Qed.


Lemma canonS_LE alpha n :
    nf alpha ->  canon alpha (S n) t1<= canon alpha (S (S n)).
  Proof.
    intro H; destruct (zero_limit_succ_dec H).
    -   destruct s. 
        +  subst; cbn. 
           apply LE_refl; auto with T1.
        + apply LE_r; eapply canonS_limit_mono; auto.
    - destruct s as [gamma [Hgamma Hgamma']]; subst .
      repeat rewrite canon_succ;auto with T1.
      apply LE_refl;auto. 
  Qed.

  (** exercise  after Guillaume Melquiond   *)
  
  Require Import Fuel. 

Fixpoint  approx alpha beta fuel i :=
  match fuel with
          FO => None
        | Fuel.FS f =>
          let gamma := canonS alpha i in
          if lt_b beta gamma
          then Some (i,gamma)
          else approx alpha beta  (f tt) (S i)
        end.


Lemma approx_ok alpha beta :
  forall fuel i j gamma, approx alpha beta fuel i = Some (j,gamma) ->
                         gamma = canonS alpha j /\ lt_b beta gamma.
Proof.
  induction fuel as [| f IHfuel ].
  - cbn; discriminate. 
  - intros i j gamma H0;  cbn in H0.
    case_eq (lt_b beta (canonS alpha i));intro H1; rewrite H1 in *.
    + injection H0; intros; subst; split;auto.
    + now specialize (IHfuel tt (S i) _ _ H0).
Qed.




  
  (** ** Adaptation to E0 (well formed terms of type [T1] ) *)
  

Open Scope E0_scope.

(** This is a helper which should be deprecated later :
    [CanonS alpha i] should be replaced by [Canon alpha (S i)] *)

Definition CanonS (alpha:E0)(i:nat): E0.
  refine (@mkord (@canonS (cnf alpha) i) _);  apply nf_canon.
  destruct alpha;auto.
Defined.

Definition Canon (alpha:E0)(i:nat): E0 :=
  match i with 0 => Zero 
          | S j => CanonS alpha j
  end.

Lemma CanonS_Canon alpha i : Canon alpha (S i) = CanonS alpha i.
Proof. reflexivity. Qed.
  
Lemma Canon_Succ beta n: Canon (Succ beta) (S n) = beta.
Proof.
  destruct beta. simpl. unfold CanonS, Succ. simpl.
  apply E0_eq_intro. simpl.
  now rewrite (canonS_succ).  
Qed.

Lemma Canon_Omega k : Canon omega k = Fin k.
Proof.
  destruct k.
  - now cbn.
  - apply E0_eq_intro; reflexivity.
Qed.

Hint Rewrite Canon_Omega : E0_rw.

Lemma CanonSSn (i:nat) :
  forall alpha n  , alpha <> Zero ->
                    CanonS (Ocons alpha (S n) Zero) i =
                    Ocons alpha n (CanonS (phi0 alpha) i).
Proof.
  intros; apply E0_eq_intro;
  unfold CanonS;repeat (rewrite cnf_rw || rewrite cnf_Ocons); auto.
  - unfold canonS; rewrite canonSSn; auto with E0.
  -  unfold lt, phi0; repeat rewrite cnf_rw. 
     apply canonS_LT ; trivial. 
     apply nf_phi0;auto with E0. 
     discriminate.
   -  unfold lt; eauto with E0.
      apply LT1; apply nf_phi0;auto with E0.
Qed. 

Lemma CanonS_phi0_lim alpha k : Limitb alpha ->
                                CanonS (phi0 alpha) k =
                                phi0 (CanonS alpha k). 
Proof.
  intro; orefl; rewrite cnf_phi0.
  unfold CanonS, canonS; repeat   rewrite cnf_rw;  rewrite <- canonS_lim1.
  -  now rewrite cnf_phi0.
  - apply cnf_ok.
  - destruct alpha; cbn; assumption. 
Qed.


Lemma CanonS_lt : forall i alpha, alpha <> Zero -> CanonS alpha i o< alpha.
Proof.
  destruct alpha. unfold Lt, CanonS. cbn.
  intro;apply canonS_LT; auto.
  intro H0; subst. apply H. unfold Zero; f_equal.
  apply nf_proof_unicity.
Qed.


Lemma Canon_lt : forall i alpha, alpha <> Zero -> Canon alpha i o< alpha.
Proof.
  destruct i.
  - unfold Canon;  intros;  destruct alpha.
    unfold Lt, Zero in *; simpl in *. 
    apply T1.not_zero_lt; auto.
    intro; subst cnf; apply H; f_equal;  eapply nf_proof_unicity.
  -   apply CanonS_lt.
Qed.

Lemma Canon_of_limit_not_null : forall i alpha, Limitb alpha ->
                                       Canon alpha (S i) <> Zero.
Proof.
  destruct alpha;simpl;unfold CanonS; simpl;  rewrite E0_eq_iff.
  simpl;   apply limitb_canonS_not_zero; auto.
Qed.

Global Hint Resolve CanonS_lt Canon_lt Canon_of_limit_not_null : E0.

Lemma CanonS_phi0_Succ alpha i : CanonS (phi0 (Succ alpha)) i =
                                 Omega_term alpha i.
Proof.      
  apply E0_eq_intro;  unfold Omega_term, CanonS, phi0, Succ, canonS.
  simpl cnf; rewrite pred_of_succ; case_eq (succ (cnf alpha)).
  - intro H; destruct (succ_not_zero _ H);  auto.
  - reflexivity. 
  - intro; apply cnf_ok.
  - intros; apply cnf_ok.
Qed.


