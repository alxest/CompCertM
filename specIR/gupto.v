Require Import Paco.paco.

Set Implicit Arguments.


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


Inductive euttF vclo (_euttF : stream -> stream -> Prop): stream -> stream -> Prop :=
| EqRet: euttF vclo _euttF snil snil
| EqVis n sl sr (REL: vclo _euttF sl sr): euttF vclo _euttF (scons n sl) (scons n sr)
| EqTau sl sr (REL: _euttF sl sr): euttF vclo _euttF (stau sl) (stau sr)
.
Hint Constructors euttF : core.

Lemma euttF_mon vclo (MON: monotone2 vclo) : monotone2 (euttF vclo).
Proof.
  intros x0 x1 r r' IN LE. induction IN; auto. econstructor; eauto.
Qed.
Hint Resolve euttF_mon : paco.

Lemma eutt_idclo_mono: monotone2 (@id (stream -> stream -> Prop)).
Proof. unfold id. eauto. Qed.

Definition eutt (sl sr: stream) := paco2 (euttF id) bot2 sl sr.
Hint Unfold eutt : core.



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

Lemma concat_nil_r
      s
  :
    s ++ [] = s
.
Proof.
  admit. (* use bisim is eq && bisim with pcofix *)
Admitted.

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
    (REL: R s0 t0)
    (REL: R s1 t1)
  :
    concatC R (concat s0 s1) (concat t0 t1)
.
Hint Constructors concatC.

Ltac inv H := inversion H; subst; clear H.

Lemma concatC_wcompat
      vclo
      (MON: monotone2 vclo)
      (CMP: compose concatC vclo <3= compose vclo concatC)
  :
    wcompatible2 (euttF vclo) concatC.
Proof.
  constructor.
  - pmonauto.
  - intros. inv PR.
    (* rewrite id_stream_eq with s0. *)
    (* rewrite id_stream_eq with t0. *)
    rewrite ! unfold_concat.
    inv REL; inv REL0; cbn; (econstructor; eauto).
    + eapply MON; eauto. intros. gbase. eauto.
    + gbase. eauto.
    + eapply MON.
      { rewrite ! concat_nil_r. eauto. }
      intros. gbase. eauto.
    + eapply MON.
      { eapply CMP. unfold compose. econstructor; eauto.
        eapply MON.
        { rewrite (@scons_concat n0 sl0).
          rewrite (@scons_concat n0 sr0).
          eapply CMP. econstructor; eauto.
          admit.
        }
        intros.
        admit.
      }
      intros.
        +
          simpl
        instantiate (1:=r). admit. }
      intros. gbase. eauto.
    +
    + gbase; eauto.
    destruct s0 eqn:S; destruct t0 eqn:T; cbn.
    { rewrite ! unfold_concat. cbn. 
    cbn.
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
