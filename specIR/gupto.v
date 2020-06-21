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
| sstuck
.

Definition match_stream (s: stream) :=
  match s with
  | snil => snil
  | scons n s => scons n s
  | stau s => stau s
  | sstuck => sstuck
  end.

Lemma unfold_stream s
  :
    s = match_stream s.
Proof.
  destruct s; auto.
Qed.


Inductive simF (_simF : stream -> stream -> Prop): stream -> stream -> Prop :=
| SimRet: simF _simF snil snil
| SimVis n sl sr (REL: _simF sl sr): simF _simF (scons n sl) (scons n sr)
| SimTau sl sr (REL: _simF sl sr): simF _simF (stau sl) (stau sr)
| SimStuck sr: simF _simF sstuck sr 
.
Hint Constructors simF : core.

Lemma simF_mon : monotone2 (simF).
Proof.
  intros x0 x1 r r' IN LE. induction IN; auto.
Qed.
Hint Resolve simF_mon : paco.

Definition sim (sl sr: stream) := paco2 (simF) bot2 sl sr.
Hint Unfold sim : core.





Global Instance Reflexive_sim : Reflexive (sim).
Proof.
  red. pcofix CIH. pfold.
  destruct x.
  - econs; eauto.
  - econs; eauto.
  - econs; eauto.
  - econs; eauto.
Qed.

Definition match_concat concat (s0 s1: stream): stream :=
  match s0 with
  | snil => s1
  | scons n s0 => scons n (concat s0 s1)
  | stau s0 => stau (concat s0 s1)
  | sstuck => sstuck
  end
.

CoFixpoint concat (s0 s1: stream): stream := match_concat concat s0 s1.

Notation "x ++ y" := (concat x y) : stream_scope.
Notation "[ ]" := snil (format "[ ]") : stream_scope.
Notation "[ x ]" := (scons x snil) : stream_scope.
Notation "[ x ; y ; .. ; z ]" := (scons x (scons y .. (scons z snil) ..)) : stream_scope.
Open Scope stream_scope.

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

Inductive concatC (R : stream -> stream -> Prop): stream -> stream -> Prop :=
| concatC_intro
    s0 s1 t0 t1
    (REL: sim s0 t0)
    (REL: R s1 t1)
  :
    concatC R (concat s0 s1) (concat t0 t1)
.
Hint Constructors concatC.

(* Lemma concatC_spec simC (*** <-- for any simC this holds? ***) vclo *)
(*       (MON: monotone2 vclo) *)
(*       (* (CMP: compose (simC) vclo <3= compose vclo (simC)) *) *)
(*       (ID: id <3= vclo) *)
(*   : *)
(*     concatC <3= gupaco2 (simF vclo) (simC) *)
(* . *)
(* Proof. *)
(*   gcofix CIH. intros. destruct PR. *)
(*   punfold REL. inv REL. *)
(*   - rewrite ! unfold_concat. cbn. gbase. eauto. *)
(*   - gstep. *)
(*     rewrite ! unfold_concat. cbn. *)
(*     econs; eauto. *)
(*     unfold id in *. pclearbot. eauto with paco. *)
(*   - gstep. *)
(*     rewrite ! unfold_concat. cbn. *)
(*     econs; eauto. *)
(*     unfold id in *. pclearbot. eauto with paco. *)
(*   - gstep. *)
(*     rewrite ! unfold_concat. cbn. *)
(*     econs; eauto. *)
(* Qed. *)
Lemma concatC_spec
      simC
  :
    concatC <3= gupaco2 (simF) (simC)
.
Proof.
  gcofix CIH. intros. destruct PR.
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
  - gstep.
    rewrite ! unfold_concat. cbn.
    econs; eauto.
Qed.

Lemma sim_concat
      s0 s1 t0 t1
      (EQ0: sim s0 t0)
      (EQ1: sim s1 t1)
  :
    @sim (concat s0 s1) (concat t0 t1)
.
Proof.
  intros. ginit. { eapply cpn2_wcompat; pmonauto. } guclo concatC_spec.
Qed.

Lemma sim_concat_proper: Proper (sim ==> sim ==> sim) concat.
Proof.
  ii. eapply sim_concat; eauto.
Qed.

