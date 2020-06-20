Require Import Paco.paco.

Set Implicit Arguments.


CoInductive stream :=
| snil
| scons (n: nat) (s: stream)
| stau (s: stream)
.

Definition id_match_stream (s: stream) :=
  match s with
  | snil => snil
  | scons n s => scons n s
  | stau s => stau s
  end.

Lemma id_stream_eq s
  :
    s = id_match_stream s.
Proof.
  destruct s; auto.
Qed.


Inductive euttF (_euttF : stream -> stream -> Prop): stream -> stream -> Prop :=
| EqRet: euttF _euttF snil snil
| EqVis n sl sr (REL: _euttF sl sr): euttF _euttF (scons n sl) (scons n sr)
| EqTau sl sr (REL: _euttF sl sr): euttF _euttF (stau sl) (stau sr)
| EqTauL sl sr (REL: euttF _euttF sl sr): euttF _euttF (stau sl) sr
| EqTauR sl sr (REL: euttF _euttF sl sr): euttF _euttF sl (stau sr)
.
Hint Constructors euttF : core.

Lemma euttF_mon : monotone2 euttF.
Proof.
  intros x0 x1 r r' IN LE. induction IN; auto.
Qed.
Hint Resolve euttF_mon : paco.

Definition eutt (sl sr: stream) := paco2 euttF bot2 sl sr.
Hint Unfold eutt : core.


CoFixpoint s0: stream := scons 0 s0'
with s0' := stau s1
with s1 := scons 1 s1'
with s1' := scons 2 s0'
.

CoFixpoint t0: stream := scons 0 t0'
with t0' := scons 1 t1'
with t1' := scons 2 t0'
.
Definition t1 := t0'.

Inductive X0: forall (sl sr: stream), Prop :=
| X0_s0_t0: X0 s0 t0
| X0_s1_t1: X0 s1 t1
.
Hint Constructors X0.

Inductive X1: forall (sl sr: stream), Prop :=
| X1_s0'_t0': X1 s0' t0'
| X1_s1'_t1': X1 s1' t1'
.
Hint Constructors X1.


Inductive TauL (R : stream -> stream -> Prop): stream -> stream -> Prop :=
| TauL_intro
    sl sr
    (REL: R sl sr)
  :
    TauL R (stau sl) sr
.
Hint Constructors TauL.

Lemma TauL_wcompat
  :
    wcompatible2 euttF TauL.
Proof.
  constructor.
  - intros x0 x1 r r' IN LE. induction IN; subst; eauto.
  - intros. inversion PR; subst.
    eapply euttF_mon; eauto. intros. gbase. auto.
Qed.

Lemma X0_eutt
  :
    X0 <2= eutt.
Proof.
  ginit. (* Init *)
  { intros. eapply TauL_wcompat. } (* weakly compatible *)
  gcofix CIH0. (* Acc *)
  gstep. (* Step *)
  cut (X1 <2= gpaco2 euttF TauL r r).
  { intros. rewrite (@id_stream_eq x2). rewrite (@id_stream_eq x3).
    inversion PR; subst; simpl; apply EqVis; apply H; auto. } (* Lemma 2.6 *)
  gcofix CIH1. (* Acc *)
  intros sl sr REL. inversion REL; subst.
  - (* lhs *)
    gclo. (* Closure* *)
    rewrite (@id_stream_eq s0'). rewrite (@id_stream_eq t0').
    simpl. constructor. (* Lemma 3.7 *)
    gbase. (* Base *)
    apply CIH0. replace (scons 1 t1') with t1; auto. rewrite (@id_stream_eq t1); auto.
  - gstep. (* Step *)
    rewrite (@id_stream_eq s1'). rewrite (@id_stream_eq t1'). simpl. apply EqVis. (* EqVis *)
    gbase. (* Base *)
    auto.
Qed.
