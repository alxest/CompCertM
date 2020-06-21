From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Export
     (* Data.String *)
     (* Structures.Monad *)
     (* Structures.Traversable *)
     (* Structures.Foldable *)
     (* Structures.Reducible *)
     OptionMonad
     Functor FunctorLaws
     Structures.Maps
     (* Data.List *)
.

From ITree Require Export
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     EqAxiom
.

Export SumNotations.
Export ITreeNotations.
Export Monads.
Export MonadNotation.
Export FunctorNotation.
Open Scope monad_scope.

Require Import MapsC.
Require Import ValuesC.
Require Import MemoryC.
Require Import CoqlibC.
Require Import ASTC.
Require Import EventsC.
Require Import GlobalenvsC.
Require Import IntegersC.
Require Import Mod ModSem Any Skeleton.

Require Import Program.
Require Import AxiomsC.

Set Implicit Arguments.












Lemma unfold_interp_mrec :
forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) 
  (R : Type) (t : itree (D +' E) R), interp_mrec ctx t = _interp_mrec ctx (observe t)
.
Proof. ii. apply bisimulation_is_eq; et. eapply unfold_interp_mrec; et. Qed.

Lemma bind_ret_r: forall (E : Type -> Type) (R : Type) (s : itree E R), x <- s;; Ret x = s.
Proof. ii. apply bisimulation_is_eq; et. eapply bind_ret_r; et. Qed.
Lemma bind_ret_l: forall (E : Type -> Type) (R S : Type) (r : R) (k : R -> itree E S),
    x <- Ret r;; k x = k r.
Proof. ii. apply bisimulation_is_eq; et. eapply bind_ret_l; et. Qed.

Ltac ides itr :=
  let T := fresh "T" in
  destruct (observe itr) eqn:T;
  sym in T; apply simpobs in T; apply bisimulation_is_eq in T; rewrite T in *; clarify.
Ltac csc := clarify; simpl_depind; clarify.
















Section eqit.

  (** Although the original motivation is to define an equivalence
      relation on [itree E R], we will generalize it into a
      heterogeneous relation [eqit_] between [itree E R1] and
      [itree E R2], parameterized by a relation [RR] between [R1]
      and [R2].

      Then the desired equivalence relation is obtained by setting
      [RR := eq] (with [R1 = R2]).
   *)
  Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

  (** We also need to do some gymnastics to work around the
      two-layered definition of [itree]. We first define a
      relation transformer [eqitF] as an indexed inductive type
      on [itreeF], which is then composed with [observe] to obtain
      a relation transformer on [itree] ([eqit_]).

      In short, this is necessitated by the fact that dependent
      pattern-matching is not allowed on [itree].
   *)

  Inductive eqit0_ vclo (sim : itree E R1 -> itree E R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
  | EqRet r1 r2
       (REL: RR r1 r2):
     eqit0_ vclo sim (Ret r1) (Ret r2)
  | EqTau m1 m2
        (REL: sim m1 m2):
      eqit0_ vclo sim (Tau m1) (Tau m2)
  | EqVis {u} (e : E u) k1 k2
        (REL: forall v, vclo sim (k1 v) (k2 v) : Prop):
      eqit0_ vclo sim (Vis e k1) (Vis e k2)
  .
  Hint Constructors eqit0_: core.



  (* Inductive eqitF (sim : itree E R1 -> itree E R2 -> Prop) : itree' E R1 -> itree' E R2 -> Prop := *)
  (* | EqRetF r1 r2 *)
  (*      (REL: RR r1 r2): *)
  (*    eqitF sim (RetF r1) (RetF r2) *)
  (* | EqTauF m1 m2 *)
  (*       (REL: sim m1 m2): *)
  (*     eqitF sim (TauF m1) (TauF m2) *)
  (* | EqVisF {u} (e : E u) k1 k2 *)
  (*       (REL: forall v, sim (k1 v) (k2 v) : Prop): *)
  (*     eqitF sim (VisF e k1) (VisF e k2) *)
  (* . *)
  (* Hint Constructors eqitF: core. *)

  (* Definition eqit_ sim : itree E R1 -> itree E R2 -> Prop := *)
  (*   fun t1 t2 => eqitF sim (observe t1) (observe t2). *)
  (* Hint Unfold eqit_: core. *)

  (* Goal forall sim i0 i1, eqit0_ sim i0 i1 = eqit_ sim i0 i1. *)
  (* Proof. *)
  (*   ii. apply prop_ext. split; i. *)
  (*   - inv H; econs; et. *)
  (*   - rr in H. *)
  (*     (* remember (observe i0) eqn:T0. remember (observe i1) eqn:T1. *) *)
  (*     inv H; destruct (observe i0) eqn:T0; ss; destruct (observe i1) eqn:T1; ss; *)
  (*       sym in T0; apply simpobs in T0; *)
  (*       sym in T1; apply simpobs in T1; *)
  (*       apply bisimulation_is_eq in T0; *)
  (*       apply bisimulation_is_eq in T1; *)
  (*       clarify; simpl_depind; clarify. *)
  (*     + econs; et. *)
  (*     + econs; et. *)
  (*     + econs; et. *)
  (* Qed. *)

  Lemma eqit0__mono vclo (MON: monotone2 vclo): monotone2 (eqit0_ vclo).
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve eqit0__mono : paco.

  Lemma eqit0_idclo_mono: monotone2 (@id (itree E R1 -> itree E R2 -> Prop)).
  Proof. unfold id. eauto. Qed.
  Hint Resolve eqit0_idclo_mono : paco.

  Definition eqit0 : itree E R1 -> itree E R2 -> Prop :=
    paco2 (eqit0_ id) bot2.

End eqit.

Hint Unfold eqit0: core.
Hint Resolve eqit0__mono : paco.
Hint Resolve eqit0_idclo_mono : paco.
Hint Unfold eqit0: core.
Hint Unfold id: core.


















Section eqit_gen.

(** *** Properties of relation transformers. *)

Context {E : Type -> Type} {R: Type} (RR : R -> R -> Prop).

Global Instance Reflexive_eqit_ (sim : itree E R -> itree E R -> Prop)
: Reflexive RR -> Reflexive sim -> Reflexive (eqit0_ RR id sim).
Proof.
  repeat red. intros.
  ides x; econs; et.
Qed.

Global Instance Symmetric_eqit_ (sim : itree E R -> itree E R -> Prop)
: Symmetric RR -> Symmetric sim -> Symmetric (eqit0_ RR id sim).
Proof.
  ii. inv H1.
  - econs; et.
  - econs; et.
  - econs; et. u in *. et.
Qed.

Global Instance Reflexive_eqit : Reflexive RR -> Reflexive (@eqit0 E _ _ RR).
Proof.
  {
    intros. pcofix CIH.
    ii. pfold.
    ides x; csc; econs; et.
  }
Qed.

Global Instance Symmetric_eqit : Symmetric RR -> Symmetric (@eqit0 E _ _ RR).
Proof.
  {
    intros. pcofix CIH.
    ii. pfold.
    punfold H1.
    (* eapply Symmetric_eqit_; eauto. *)
    ides x; inv H1; csc.
    - econs; et.
    - econs; et. pclearbot. right. eapply CIH. et.
    - econs; et. ii. spc REL. pclearbot. right. eapply CIH. et.
  }
Qed.

Global Instance eqit_bind {S} :
  Proper (pointwise_relation _ (eqit0 eq) ==>
          eqit0 eq ==> eqit0 eq) (@ITree.bind' E R S).
Proof.
  pcofix CIH.
  ii. pfold. punfold H1. inv H1; ss.
  - setoid_rewrite (bind_ret_l). (*** TODO: unnecessary setoid rewrite ***)
    rr in H0. spc H0. punfold H0.
    eapply eqit0__mono; eauto.
Abort.

Lemma eqit_bind' {S1 S2}
      (RS : S1 -> S2 -> Prop)
      t1 t2 k1 k2 :
  eqit0 RR t1 t2 ->
  (forall r1 r2, RR r1 r2 -> eqit0 RS (k1 r1) (k2 r2)) ->
  @eqit0 E _ _ RS (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  {
    pcofix CIH.
    ii. pfold.
    punfold H0. inv H0; ss.
    - setoid_rewrite (bind_ret_l). (*** TODO: unnecessary setoid rewrite ***)
      exploit H1; et. intro T. rr in T.
Abort.


Inductive eqit0C (r : itree E R -> itree E R -> Prop) :
  itree E R -> itree E R -> Prop :=
| pbc_intro_h U1 U2 (RU : U1 -> U2 -> Prop) t1 t2 k1 k2
              (EQV: eqit0 RU t1 t2)
              (REL: forall u1 u2, RU u1 u2 -> r (k1 u1) (k2 u2))
  : eqit0C r (ITree.bind t1 k1) (ITree.bind t2 k2)
.

Lemma eqit0C_mon r1 r2 t1 t2
      (IN: eqit0C r1 t1 t2)
      (LE: r1 <2= r2):
  eqit0C r2 t1 t2.
Proof.
  destruct IN. econstructor; eauto.
Qed.

Hint Resolve eqit0C_mon : paco.

Lemma eqit0_bind_clo_wcompat vclo
      (MON: monotone2 vclo)
      (CMP: compose (eqit0C) vclo <3= compose vclo (eqit0C)):
  wcompatible2 (@eqit0_ E R R RR vclo) (eqit0C).
Proof.
  econstructor.
  { pmonauto. ii. eapply eqit0C_mon; et. }
  intros. dependent destruction PR.
  punfold EQV.
  {
    inv EQV; ii.
    - setoid_rewrite bind_ret_l.
  }
  hinduction REL before r; intros; clear t1' t2'.
  - remember (RetF r1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; eauto.
    remember (RetF r3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; eauto.
  - remember (TauF m1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; eauto.
    remember (TauF m3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; eauto.
    pclearbot. econstructor. gclo.
    econstructor; cycle -1; eauto with paco.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; subst; try dependent destruction Heqx; try inv CHECK; eauto.
    remember (VisF e0 k3) as y.
    hinduction EQVr before r; intros; subst; try dependent destruction Heqy; try inv CHECK; eauto.
    econstructor. intros. pclearbot.
    eapply MON.
    + apply CMP. econstructor; eauto.
    + intros. apply gpaco2_clo, PR.
  - remember (TauF t1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; eauto.
    pclearbot. punfold REL.
  - remember (TauF t2) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; eauto.
    pclearbot. punfold REL.

  econs; et.
  { ii. inv IN. econs; et. }
  ii.
Qed.

Lemma eqit0_clo_bind b1 b2 vclo
      (MON: monotone2 vclo)
      (CMP: compose (eqitC RR b1 b2) vclo <3= compose vclo (eqitC RR b1 b2))
      (ID: id <3= vclo):
  eqit0_bind_clo <3= gupaco2 (eqit_ RR b1 b2 vclo) (eqitC RR b1 b2).
Proof.

Lemma eqit0_clo_bind: wcompatible2 (eqit0_ eq) eqit0_bind_clo.
Proof.
  econstructor.
  { ii. inv IN. econs; et. }
  ii. depdes PR.
  punfold EQV. inv EQV.
  - setoid_rewrite bind_ret_l. exploit REL; et. intro T. eapply REL.
    econs; et.
Qed.


TODO: study
eqit_bind_clo
eqit_clo_bind
  }
  intros. ginit. guclo eqit_clo_bind. unfold eqit in *.
  econstructor; eauto with paco.
Qed.

End eqit_gen.






















Section Facts.

Context {D E : Type -> Type} (ctx : D ~> itree (D +' E)).

Global Instance eq_itree_mrec {R} :
  Proper (eqit0 eq ==> eqit0 eq) (@interp_mrec _ _ ctx R).
Proof.
  {
    pcofix CIH. ii. pfold.
    rewrite !unfold_interp_mrec.
    punfold H0; inv H0; ss.
    - econs; et.
    - econs; et. pclearbot. right. eapply CIH; et.
    - des_ifs.
      + econs; et. pclearbot. right. eapply CIH; et.
        pfold. econs; et.
  }
  ginit.
  (* { ii. eapply cpn2_wcompat; et. eauto with paco. } *)
  (* { instantiate (1:= bot3). ii. econs; et. ii; ss. } *)
  gcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  punfold H0. inv H0; try discriminate; pclearbot; simpobs; [| |destruct e]; gstep.
  - apply reflexivity.
  - econstructor. eauto with paco.
  - econstructor. gbase. eapply CIH. apply eqit_bind; auto; reflexivity.
  - econstructor. gstep; constructor. auto with paco.
Qed.


End Facts.

