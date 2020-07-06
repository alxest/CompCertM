From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

Require Import MapsC.
Require Import ValuesC.
Require Import MemoryC.
Require Import CoqlibC.
Require Import ASTC.
Require Import EventsC.
Require Import GlobalenvsC.
Require Import IntegersC.
Require Import Mod ModSem Any Skeleton.
Require Import SimMem SimSymb Sound.
Require SimMemId SimSymbId SoundTop.
Require Import SimMod SimModSem.
Require Import SIRCommon SimSIR SIR.

Require Import Program.
Require Import Simulation.

Set Implicit Arguments.






Section LEXSTK.
  (** exponential? **)

  Variable idx: Type.
  Variable ord: idx -> idx -> Prop.
  Hypothesis WF: well_founded ord.

  Definition eidx: Type := list idx.

  Inductive eord: eidx -> eidx -> Prop :=
  | eord_hd
      hd0 hd1
      (ORD: ord hd0 hd1)
      tl
    :
      eord (hd0 :: tl) (hd1 :: tl)
  | eord_call
      hd0 hd1
      (ORD: ord hd0 hd1)
      tl
    :
      eord (hd0 :: hd0 :: tl) (hd1 :: tl)
  | eord_ret
      hd tl
    :
      eord tl (hd :: tl)
  .

  Theorem ord_lex_wf: <<WF: well_founded eord>>.
  Proof.
    assert(ACC0: forall n, (forall x, (List.length x < n)%nat -> Acc eord x) ->
                           (forall x, (List.length x = n)%nat -> Acc eord x)
          ).
    {
      induction 0.
      { ii. destruct x; ss. econs; et. ii. inv H1. }
      ii. destruct x; ss. clarify.
      econs; et. ii. inv H0.
      - econs. ii. inv H0.
    }
    assert(ACC0: forall x, Acc ord x -> Acc eord [x] -> Acc eord [x ; x]).
    {
      induction 1. induction 1.
      econs; et. ii. inv H3; et.
      - et.
    }
    assert(ACC: forall a xs, Acc ord a -> Acc eord xs -> Acc eord (a :: xs)).
    {
      induction 0.
      { i. clear H0. induction H. econs; et. ii. inv H1; et.
        - exploit H; et. intro T.
          exploit H0; et. intro U. clear H H0 ORD.
        induction 1. induction 1.
        econs; et. ii. inv H3; et.
        ii.
        ii. econs; et. ii. inv H1; ss.
        - econs; et.
    }
    assert(ACC: forall xs, (forall x (IN: In x xs), Acc ord x) -> Acc eord xs).
    {
      induction 0.
      { ii; ss. econs; et. ii; ss. inv H0. }
      induction 0.
      - ii. econs. ii. inv H2.
        +
      econs; et.
      ii. inv H0.
      - econs; et.
      induction 0.
      econs. i. inv H3.
      - eauto.
      - eauto.
    }
    rr. i. destruct a. eapply ACC; eauto.
  Qed.

End LEXICO.





Local Obligation Tactic := ii; ss; eauto.

Local Open Scope signature_scope.



Section OWNEDHEAP.

Variable mi: string.
Variable owned_heap: Type.
Variable _pures: ident -> Prop.
(* Let idx := nat. *)
(* Let ord := lt. *)
Variable idx: Type.
Variable ord: idx -> idx -> Prop.
Hypothesis wf_ord: well_founded ord.
Let sim_st := sim_st (@eq owned_heap).





(*** sim syntax ***)
Section SYNTAX.

(*** sim itree ***)
Section REL.

Context `{S: Type}.
Let itr := itree (E owned_heap) S.

(* Inductive _pure (pure: idx -> itr -> Prop) (i0: idx): itr -> Prop := *)
(* | pure_ret *)
(*     s *)
(*   : *)
(*     _pure pure i0 (Ret s) *)
(* | pure_tau *)
(*     i1 *)
(*     (ORD: ord i1 i0) *)
(*     itr *)
(*     (PURE: pure i1 itr) *)
(*   : *)
(*     _pure pure i0 (Tau itr) *)
(* | pure_icall *)
(*     fname oh0 m0 vs0 ktr *)
(*     (PURE: forall ohmv, exists i1, <<ORD: ord i1 i0>> /\ <<PURE: pure i1 (ktr ohmv)>>) *)
(*   : *)
(*     _pure pure i0 (Vis (subevent _ (ICall fname oh0 m0 vs0)) ktr) *)
(* | pure_nb *)
(*     ktr *)
(*   : *)
(*     _pure pure i0 (Vis (subevent _ (ENB)) ktr) *)
(* . *)

(* Definition pure: idx -> itr -> Prop := paco2 _pure bot2. *)
(* Lemma pure_mon: monotone2 _pure. *)
(* Proof. *)
(*   ii. inv IN; try (by econs; et; rr; et). *)
(*   -  econs; et. i. exploit PURE; et. i; des. esplits; et. *)
(* Qed. *)
(* Hint Unfold pure. *)
(* Hint Resolve pure_mon: paco. *)



(* Theorem pure_bind *)
(*         a itr ktr T *)
(*         (PURE: pure a itr) *)
(*         (PURE: forall x, exists b, pure b (ktr x)) *)
(*         b *)
(*   : *)
(*     <<PURE: pure (a + b) (x <- itr ;; ktr)>> *)
(* . *)
(* Proof. *)
(*   red. ginit. *)
(*   { intros. eapply cpn2_wcompat; eauto with paco. } *)
(*   guclo bindC_spec. ii. econs; et. *)
(*   u. ii. *)
(*   exploit H0; et. i. eauto with paco. *)
(* Qed. *)

Inductive pure (i0: idx): itr -> Prop :=
| pure_ret
    s
  :
    pure i0 (Ret s)
| pure_tau
    i1
    (ORD: ord i1 i0)
    itr
    (PURE: pure i1 itr)
  :
    pure i0 (Tau itr)
| pure_icall
    fname oh0 m0 vs0 ktr
    (PURE: forall ohmv, exists i1, <<ORD: ord i1 i0>> /\ <<PURE: pure i1 (ktr ohmv)>>)
  :
    pure i0 (Vis (subevent _ (ICall fname oh0 m0 vs0)) ktr)
| pure_nb
    ktr
  :
    pure i0 (Vis (subevent _ (ENB)) ktr)
.
Hint Constructors pure.

(* Inductive pureN (i0: idx): itr -> nat -> Prop := *)
(* | pureN_ret *)
(*     s *)
(*   : *)
(*     pureN i0 (Ret s) (0%nat) *)
(* | pureN_tau *)
(*     i1 *)
(*     (ORD: ord i1 i0) *)
(*     n itr *)
(*     (PURE: pureN i1 itr n) *)
(*   : *)
(*     pureN i0 (Tau itr) (1 + n)%nat *)
(* | pureN_icall *)
(*     fname oh0 m0 vs0 ktr n *)
(*     (PURE: forall ohmv, exists i1, <<ORD: ord i1 i0>> /\ <<PURE: pureN i1 (ktr ohmv) n>>) *)
(*   : *)
(*     pureN i0 (Vis (subevent _ (ICall fname oh0 m0 vs0)) ktr) (1 + n) *)
(* | pureN_nb *)
(*     ktr *)
(*   : *)
(*     pureN i0 (Vis (subevent _ (ENB)) ktr) 0%nat *)
(* . *)
(* Hint Constructors pureN. *)

(* Theorem pure_pureN *)









Inductive _match_itr (match_itr: itr -> itr -> Prop): itr -> itr -> Prop :=
| match_ret
    s
  :
    _match_itr match_itr (Ret s) (Ret s)
| match_tau
    i_src
    i_tgt
    (MATCH: match_itr i_src i_tgt)
  :
    _match_itr match_itr (Tau i_src) (Tau i_tgt)
| match_vis
    X (e: (E owned_heap) X) k_src k_tgt
    (MATCH: (eq ==> match_itr)%signature k_src k_tgt)
  :
    _match_itr match_itr (Vis e k_src) (Vis e k_tgt)
| match_icall_pure
    fname oh0 m0 vs0 i_src i_tgt
    (PURE: _pures fname)
    (MATCH: match_itr i_src i_tgt)
  :
    _match_itr match_itr
               (trigger (ICall fname oh0 m0 vs0) >>= (fun _ => i_src))
               (tau;; i_tgt)
.

Definition match_itr: itr -> itr -> Prop := paco2 _match_itr bot2.
Lemma match_itr_mon: monotone2 _match_itr.
Proof.
  ii. inv IN; try (by econs; et; rr; et).
Qed.

End REL.

Hint Unfold pure.
Hint Resolve pure_mon: paco.
Hint Unfold match_itr.
Hint Resolve match_itr_mon: paco.












Section PROG.

Definition match_fn: relation (function owned_heap) := (eq ==> eq ==> eq ==> match_itr).

Inductive match_prog (p_src p_tgt: program owned_heap): Prop :=
| match_prog_intro
    (PURES: forall
        _fn fn
        (PURE: _pures _fn)
        (SOME: p_tgt _fn = Some fn)
      ,
        forall oh m vs, exists i, pure i (fn oh m vs))
    (MATCH: (eq ==> option_rel match_fn) p_src p_tgt)
.

End PROG.



(*** useful lemma for below proof ***)
(*** copied from "eqit_bind_clo" in itree repo - Eq.v ***)

Context `{S : Type}.
Let itr := itree (E owned_heap) S.
Inductive bindC (r: itr -> itr -> Prop) : itr -> itr -> Prop :=
| bindC_intro
    U
    i_src i_tgt
    (SIM: match_itr i_src i_tgt)
    k_src k_tgt
    (SIMK: ((@eq U) ==> r) k_src k_tgt)
  :
    bindC r (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt)
.

Hint Constructors bindC: core.

Lemma bindC_spec
      simC
  :
    bindC <3= gupaco2 (_match_itr) (simC)
.
Proof.
  gcofix CIH. intros. destruct PR.
  punfold SIM. inv SIM.
  - rewrite ! bind_ret_l. gbase. eapply SIMK; et.
  - rewrite ! bind_tau. gstep. econs; eauto. pclearbot.
    (* gfinal. left. eapply CIH. econstructor; eauto. *)
    debug eauto with paco.
  - rewrite ! bind_vis. gstep. econs; eauto. ii. clarify.
    repeat spc MATCH. hexploit1 MATCH; ss. pclearbot. eauto with paco.
  - rewrite ! bind_bind. gstep.
    erewrite f_equal2; try eapply match_icall_pure; try refl; ss.
    { pclearbot. eauto with paco. }
    irw. ss.
Qed.

Global Instance match_itr_bind T :
  Proper ((eq ==> match_itr) ==> (match_itr) ==> (match_itr)) (ITree.bind' (T:=T) (U:=S))
.
Proof.
  red. ginit.
  { intros. eapply cpn2_wcompat; eauto with paco. }
  guclo bindC_spec. ii. econs; et.
  u. ii.
  exploit H0; et. i. eauto with paco.
Qed.

End SYNTAX.
Hint Unfold match_itr.
Hint Resolve match_itr_mon: paco.









Section SIM.

  Variable p_src: program owned_heap.
  Variable p_tgt: program owned_heap.
  Hypothesis (SIMP: match_prog p_src p_tgt).
  (* Hypothesis (WFSRC: wf_prog p_src). *)

  Lemma match_prog_sim_st
        i0 i_src i_tgt
        (SIM: match_itr i_src i_tgt)
    :
      sim_st lt i0 (interp_mrec (interp_function p_src) i_src)
             (interp_mrec (interp_function p_tgt) i_tgt)
  .
  Proof.
    revert_until SIMP.
    ginit.
    { intros. eapply cpn3_wcompat; et. eauto with paco. }
    gcofix CIH.
    i. rewrite ! unfold_interp_mrec.
    punfold SIM. inv SIM; cbn.
    - gstep. destruct s as [oh [m v]]. econs; et.
    - gstep. econs; et. gbase. pclearbot. et.
    - gstep. des_ifs.
      + econs; et. gbase.
        eapply CIH. eapply match_itr_bind; et.
        { ii. clarify. repeat spc MATCH. hexploit1 MATCH; ss. pclearbot. et. }
        destruct i.
        inv SIMP.
        exploit (MATCH0 name); et. intro T. rr in T. cbn. des_ifs; cycle 1.
        { pfold. econs; et. ii; ss. }
        exploit T; et.
      + destruct s.
        * destruct e. econs; et. ii. rr in H. des_ifs. des; clarify.
          gstep; econs; et. exploit (MATCH (o0, (m1, v0))); et. intro T. pclearbot.
          eauto with paco.
        * destruct e.
          { econs; et. }
          { econs; et. }
          { econs; et. ii.
            esplits; et. exploit (MATCH x_tgt); et. intro T. pclearbot.
            gstep. econs; et.
            eauto with paco. }
    - pclearbot.
      des_ifs; cycle 1.
      { admit "ez -- add more condition". }
      inv SIMP. exploit (MATCH0 fname); et. intro T. rr in T. des_ifs. des.
      exploit PURES; et. i; des.
      gstep. econs; et.
      irw.
          eauto with paco. gbase. eapply CIH. econs; et.
    - step_guarantee. irw. step.
      rewrite <- ! unfold_interp_mrec.
      gbase. eapply CIH.
      inv SIMP.
      des_ifs_safe. inv FOCUS. rewrite TGT. irw.
      step_assume; ss. irw.
      eapply match_itr_bind; et.
      { ii. clarify. step_guaranteeK; ss.
        (*** TODO: fix step_guaranteeK ***)
        { pfold. unfold triggerNB. rewrite bind_vis. econs; et. }
        irw. step_assume; ss.
        irw. exploit MATCH; et. intro U. pclearbot. eauto.
      }
      exploit SIM; et.
    - gstep. econs; et. u in *. gstep. econs; et.
      assert(a0 = a1).
      { rr in H0. des_ifs. des. clarify. }
      clarify.
      repeat spc MATCH. hexploit1 MATCH; ss. pclearbot.
      gbase. eapply CIH. eauto with paco.
    - gstep. econs; et.
    - gstep. econs; et.
    - irw. step. step. ii. esplits; et. step.
      exploit MATCH; et. intro T. pclearbot. eauto with paco.
  Unshelve.
    all: ss.
    all: try (by econs).
  Qed.

  (*** The result that we wanted -- allows reasoning each function "locally" and then compose ***)
  Theorem adequacy_local_local:
    forall
      (fname: ident) m vs oh
    ,
      (<<SIM: sim_st lt 1%nat (interp_program p_src (ICall fname oh m vs))
                     (interp_program p_tgt (ICall fname oh m vs))
                     >>)
  .
  Proof.
    {
      ii.
      destruct (eq_block fname _fn).
      {
        clarify.
        dup SIMP. inv SIMP0.
        unfold interp_program, interp_function, mrec.
        irw. des_ifs. inv FOCUS. rewrite TGT.
        unfold fn_src. cbn.
        unfold assume. des_ifs; cycle 1.
        { irw. pfold. unfold triggerUB. irw. econs; et. }
        rewrite ! bind_ret_l.
        irw.
        pfold. econs; et. left.
        des_ifs.
        rewrite <- ! unfold_interp_mrec.
        eapply match_prog_sim_st; ss.
        eapply match_itr_bind.
        { ii. clarify. step_guaranteeK.
          - pfold. econs; et.
          - unfold guaranteeK. des_ifs. pfold. econs; et.
        }
        eapply SIM; et.
      }
      eapply match_prog_sim_st; ss.
      inv SIMP.
      destruct (eq_block fname _fn_ru).
      { des_ifs. pfold. econs; et. }
      exploit OTHERS; et. intro T. rr in T. des_ifs; cycle 1.
      { pfold. econs; et. }
      exploit T; et.
    }
  Qed.

  Variable ioh: SkEnv.t -> owned_heap.
  Variable sk: Sk.t.
  Let md_src: Mod.t := (SIR.module sk p_src mi ioh).
  Let md_tgt: Mod.t := (SIR.module sk p_tgt mi ioh).
  Let mp: ModPair.t := (SimSymbId.mk_mp md_src md_tgt).

  Theorem sim_mod: ModPair.sim mp.
  Proof.
    eapply SimSIR.sim_mod with (SO:=eq); eauto.
    { eapply lt_wf. }
    ii. clarify. esplits. eapply adequacy_local_local; et.
  Qed.

  Theorem correct: rusc defaultR [md_src] [md_tgt].
  Proof. eapply AdequacyLocal.relate_single_rusc; try exists mp; esplits; eauto using sim_mod. Qed.

End SIM.
End OWNEDHEAP.
Hint Unfold match_itr match_fn.
Hint Constructors match_fn_focus match_prog.
Hint Resolve match_itr_mon: paco.
Hint Constructors bindC: core.
