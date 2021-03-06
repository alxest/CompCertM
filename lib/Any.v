Require Import sflib CoqlibC.
Require Import Program.
Require Import ClassicalDescription EquivDec.

Set Implicit Arguments.

Notation Any := { ty: Type & ty }.
(* Definition Any := { ty: Type & ty }. *)
(* Hint Unfold Any. *)

Definition downcast {T: Type} (a: Any): option T.
  destruct a.
  destruct (excluded_middle_informative (x = T)).
  - subst. apply Some. assumption.
  - apply None.
Defined.

Definition upcast {T} (a: T): Any := existT (fun x => x) _ a.
(* Hint Unfold downcast upcast. *)

Lemma downcast_spec
      a T (t: T)
      (CAST: downcast a = Some t)
  :
    <<TY: projT1 a = T>> /\ <<VAL: projT2 a ~= t>>
.
Proof.
  unfold downcast in *. des_ifs. ss.
  simpl_depind. eauto.
Qed.

Lemma downcast_intro
      a T (t: T)
      (TY: projT1 a = T)
      (VAL: projT2 a ~= t)
  :
    <<CAST: downcast a = Some t>>
.
Proof.
  unfold downcast in *. des_ifs. ss.
  dependent destruction e. ss.
Qed.

Lemma upcast_downcast
      T (a: T)
  :
    downcast (upcast a) = Some a
.
Proof.
  eapply downcast_intro; ss.
Qed.

Lemma projT1_upcast
      (a: Any)
  :
    <<CAST: exists t: projT1 a, a = upcast t>>
.
Proof.
  unfold upcast in *. dependent destruction a. ss. eauto.
Qed.

Lemma upcast_intro
      (a: Any)
  :
    <<CAST: a = upcast (projT2 a)>>
.
Proof.
  unfold upcast in *. dependent destruction a. ss.
Qed.

Lemma upcast_downcast_iff
      (a: Any) T (t: T)
  :
    <<UPCAST: a = upcast t>> <-> <<DOWNCAST: downcast a = Some t>>
.
Proof.
  split; ii; des.
  - clarify. rewrite upcast_downcast. ss.
  - apply downcast_spec in H. des. r.
    rewrite upcast_intro with a. unfold upcast. simpl_depind. f_equal. ss.
Qed.

Definition Any_dec (a0 a1: Any): {a0=a1} + {a0<>a1}.
  destruct a0, a1.
  simpl_depind.
  destruct (excluded_middle_informative (x = x0)).
  - clarify.
    destruct (excluded_middle_informative (p = p0)).
    + clarify. left. rewrite sigT_eta. ss.
    + right. ii. simpl_depind. clarify.
  - right. ii. simpl_depind.
Defined.

Goal (upcast tt = upcast 0 -> False).
  ii. Fail timeout 1 clarify.
Abort.

Lemma upcast_inj
      A B (a: A) (b: B)
      (EQ: upcast a = upcast b)
  :
    <<EQ: A = B>> /\ <<EQ: a ~= b>>
.
Proof. unfold upcast in *. simpl_depind. ss. Qed.

Lemma upcast_projT1
      A (a: A)
  :
    <<EQ: projT1 (upcast a) = A>>
.
Proof. ss. Qed.

Lemma upcast_projT2
      A (a: A)
  :
    <<EQ: projT2 (upcast a) = a>>
.
Proof. ss. Qed.

Lemma Any_eta
      (a0 a1: Any)
      (EQTY: projT1 a0 = projT1 a1)
      (EQVAL: projT2 a0 ~= projT2 a1)
  :
    <<EQ: a0 = a1>>
.
Proof.
  destruct a0, a1; ss.
  clarify. eapply JMeq_eq in EQVAL. clarify.
Qed.

Lemma upcast_eta
      A B a b
      (EQTY: A = B)
      (EQVAL: a ~= b)
  :
    <<EQ: @upcast A a = @upcast B b>>
.
Proof.
  eapply Any_eta; ss.
Qed.


(* Global Opaque upcast downcast. *)

(* Goal (upcast tt = upcast 0 -> False). *)
(*   ii. clarify. (* at least it terminates *) *)
(*   Undo 1. *)
(*   apply_all_once upcast_inj; des. *)
(* Abort. *)

Ltac clarify := repeat des_u;
                repeat match goal with
                       | [ H: upcast ?A = upcast ?B |- _ ] => apply upcast_inj in H; desH H
                       end; sflib.clarify.

Global Opaque upcast.

