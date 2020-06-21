Require Import Paco.paco.
Require Import Program.
Require Import RelationClasses.
Require Import Morphisms.

Set Implicit Arguments.

Ltac inv H := inversion H; subst; clear H.
Ltac econs := econstructor.
Ltac ii := repeat intro.
Ltac i := intros.
Lemma hexploit_mp: forall P Q: Type, P -> (P -> Q) -> Q.
Proof. intuition. Defined.
Ltac hexploit x := eapply hexploit_mp; [eapply x|].




CoInductive stream :=
| snil
| scons (n: nat) (s: stream)
| stau (s: stream)
.

Definition match_stream (s: stream) :=
  match s with
  | snil => snil
  | scons n s => scons n s
  | stau s => stau s
  end.

Lemma unfold_stream s
  :
    s = match_stream s.
Proof.
  destruct s; auto.
Qed.


Inductive eqitF vclo (_eqitF : stream -> stream -> Prop): stream -> stream -> Prop :=
| EqRet: eqitF vclo _eqitF snil snil
| EqVis n sl sr (REL: vclo _eqitF sl sr): eqitF vclo _eqitF (scons n sl) (scons n sr)
| EqTau sl sr (REL: _eqitF sl sr): eqitF vclo _eqitF (stau sl) (stau sr)
.
Hint Constructors eqitF : core.

Lemma eqitF_mon vclo (MON: monotone2 vclo) : monotone2 (eqitF vclo).
Proof.
  intros x0 x1 r r' IN LE. induction IN; auto. econstructor; eauto.
Qed.
Hint Resolve eqitF_mon : paco.

Lemma eqit_idclo_mono: monotone2 (@id (stream -> stream -> Prop)).
Proof. unfold id. eauto. Qed.
Hint Resolve eqit_idclo_mono : paco.

Definition eqit (sl sr: stream) := paco2 (eqitF id) bot2 sl sr.
Hint Unfold eqit : core.






Section eqit_closure.

Inductive eqitC (r: stream -> stream -> Prop)
  : stream -> stream -> Prop :=
| eqit_trans_clo t1 t2 t1' t2'
      (EQVl: eqit t1 t1')
      (EQVr: eqit t2 t2')
      (REL: r t1' t2')
  : eqitC r t1 t2
.
Hint Constructors eqitC: core.

Lemma eqitC_mon r1 r2 t1 t2
      (IN: eqitC r1 t1 t2)
      (LE: r1 <2= r2):
  eqitC r2 t1 t2.
Proof.
  destruct IN. econstructor; eauto.
Qed.
Hint Resolve eqitC_mon : paco.

Lemma eqitC_wcompat
      vclo
      (MON: monotone2 vclo)
      (CMP: compose (eqitC) vclo <3= compose vclo (eqitC))
  :
    wcompatible2 (@eqitF vclo) (eqitC)
.
Proof.
  econstructor.
  { pmonauto. }
  intros. dependent destruction PR.
  punfold EQVl. punfold EQVr.
  {
    inv REL.
    - inv EQVl. inv EQVr. econs; eauto.
    - inv EQVl. inv EQVr. econs; eauto.
      unfold id in *. pclearbot.
      eapply MON.
      { apply CMP. econs; eauto. }
      { intros. gclo. eapply eqitC_mon; eauto. intros. gbase. eauto. }
    - inv EQVl. inv EQVr. pclearbot.
      econs; eauto. gclo. econs; eauto.
      gbase. eauto.
  }
Qed.
Hint Resolve eqitC_wcompat : paco.

Lemma eqit_idclo_compat : compose (eqitC) id <3= compose id (eqitC).
Proof.
  intros. apply PR.
Qed.
Hint Resolve eqit_idclo_compat : paco.

Lemma eqitC_dist :
  forall r1 r2, eqitC (r1 \2/ r2) <2= (eqitC r1 \2/ eqitC r2).
Proof.
  intros. destruct PR. destruct REL; eauto.
Qed.
Hint Resolve eqitC_dist : paco.

Lemma eqit_clo_trans vclo
      (MON: monotone2 vclo)
      (CMP: compose (eqitC) vclo <3= compose vclo (eqitC)):
  eqitC <3= gupaco2 (eqitF vclo) (eqitC).
Proof.
  intros. destruct PR. gclo. econstructor; eauto with paco.
Qed.

End eqit_closure.

Hint Constructors eqitC: core.
Hint Resolve eqitC_mon : paco.
Hint Resolve eqitC_wcompat : paco.
Hint Resolve eqit_idclo_compat : paco.
Hint Resolve eqitC_dist : paco.








Global Instance Reflexive_eqit : Reflexive (eqit).
Proof.
  red. ginit. gcofix CIH.
  destruct x.
  - gstep. econs; eauto.
  - gstep. econs; eauto. unfold id. gbase. eauto.
  - gstep. econs; eauto. unfold id. gbase. eauto.
Qed.


(* CoFixpoint concat (s0 s1: stream): stream := *)
(*   match s0 with *)
(*   | snil => s1 *)
(*   | scons n s0 => scons n (concat s0 s1) *)
(*   | stau s0 => stau (concat s0 s1) *)
(*   end *)
(* . *)
Definition match_concat concat (s0 s1: stream): stream :=
  match s0 with
  | snil => s1
  | scons n s0 => scons n (concat s0 s1)
  | stau s0 => stau (concat s0 s1)
  end
.

CoFixpoint concat (s0 s1: stream): stream := match_concat concat s0 s1.

Notation "x ++ y" := (concat x y) : stream_scope.
Notation "[ ]" := snil (format "[ ]") : stream_scope.
Notation "[ x ]" := (scons x snil) : stream_scope.
Notation "[ x ; y ; .. ; z ]" := (scons x (scons y .. (scons z snil) ..)) : stream_scope.
Open Scope stream_scope.
(* Require Import List. *)
(* Import ListNotations. *)

Lemma unfold_concat: forall s0 s1, s0 ++ s1 = match_concat concat s0 s1.
Proof.
  intros.
  rewrite unfold_stream with (concat s0 s1). simpl.
  destruct (match_concat concat s0 s1) eqn:T; reflexivity.
Qed.

Lemma scons_concat
      n s
  :
    (scons n s) = concat [ n ] s
.
Proof.
  rewrite unfold_concat; cbn. rewrite unfold_concat; cbn. reflexivity.
Qed.

(* Lemma concat_assoc *)
(*       s0 s1 s2 *)
(*   : *)
(*     (s0 ++ s1) ++ s2 = s0 ++ s1 ++ s2 *)
(* . *)
(* Proof. *)
(*   admit. *)
(* Admitted. *)






(* Lemma concat_nil_r *)
(*       s *)
(*   : *)
(*     s ++ [] = s *)
(* . *)
(* Proof. *)
(*   admit. (* use bisim is eq && bisim with pcofix *) *)
(* Admitted. *)

(* CoFixpoint s0: stream := scons 0 s0' *)
(* with s0' := stau s1 *)
(* with s1 := scons 1 s1' *)
(* with s1' := scons 2 s0' *)
(* . *)

(* CoFixpoint t0: stream := scons 0 t0' *)
(* with t0' := scons 1 t1' *)
(* with t1' := scons 2 t0' *)
(* . *)
(* Definition t1 := t0'. *)

(* Inductive X0: forall (sl sr: stream), Prop := *)
(* | X0_s0_t0: X0 s0 t0 *)
(* | X0_s1_t1: X0 s1 t1 *)
(* . *)
(* Hint Constructors X0. *)

(* Inductive X1: forall (sl sr: stream), Prop := *)
(* | X1_s0'_t0': X1 s0' t0' *)
(* | X1_s1'_t1': X1 s1' t1' *)
(* . *)
(* Hint Constructors X1. *)


Inductive concatC (R : stream -> stream -> Prop): stream -> stream -> Prop :=
| concatC_intro
    s0 s1 t0 t1
    (REL: eqit s0 t0)
    (REL: R s1 t1)
  :
    concatC R (concat s0 s1) (concat t0 t1)
.
Hint Constructors concatC.

Lemma concatC_spec vclo
      (MON: monotone2 vclo)
      (CMP: compose (eqitC) vclo <3= compose vclo (eqitC))
      (ID: id <3= vclo)
  :
    concatC <3= gupaco2 (eqitF vclo) (eqitC)
.
Proof.
  gcofix CIH. intros. destruct PR.
  guclo eqit_clo_trans.
  econs; eauto; try reflexivity.
  punfold REL. inv REL.
  - rewrite ! unfold_concat. cbn. gbase. eauto.
  - gstep.
    rewrite ! unfold_concat. cbn.
    econs; eauto.
    unfold id in *. pclearbot. eauto with paco.
  - gstep.
    rewrite ! unfold_concat. cbn.
    econs; eauto.
    unfold id in *. pclearbot. eauto with paco.
Qed.

Lemma eqit_concat
      s0 s1 t0 t1
      (EQ0: eqit s0 t0)
      (EQ1: eqit s1 t1)
  :
    @eqit (concat s0 s1) (concat t0 t1)
.
Proof.
  intros. ginit. guclo concatC_spec.
Qed.

Lemma eqit_concat_proper: Proper (eqit ==> eqit ==> eqit) concat.
Proof.
  ii. eapply eqit_concat; eauto.
Qed.

