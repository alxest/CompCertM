Require Import SimMem.
Require Import Simulation.
Require Import AST.
From Paco Require Import paco.
Require Import sflib.
Require Import Basics.
Require Import CoqlibC.
Require Import Values Integers.
Require Import Globalenvs.
Require Import Program.
Require Import MemoryC.

Require Import Skeleton SimSymb Ord.
Require Import ModSem.
Require Import Sound Preservation.
Import ModSem.
Require Import ModSemProps.
Require Import Events.
Require Import SmallstepC.
Require Import Any.
Require Export SimModSem.

Set Implicit Arguments.


Section SIMMODSEM.

  Variables ms_src ms_tgt: ModSem.t.
  Context {SM: SimMem.class}.
  Context {SMO: SimMemOh.class}.
  Context {SS: SimSymb.class SM}.
  Variable sound_states: ms_src.(state) -> Prop.

  (* Record mem_compat (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (sm0: SimMem.t): Prop := { *)
  (*   mcompat_src: <<MCOMPATSRC: ms_src.(get_mem) st_src0 = sm0.(SimMem.src)>>; *)
  (*   mcompat_tgt: <<MCOMPATTGT: ms_tgt.(get_mem) st_tgt0 = sm0.(SimMem.tgt)>>; *)
  (* } *)
  (* . *)

  Let midx := SimMemOh.midx.

  Inductive fsim_step (fsim: idx -> state ms_src -> state ms_tgt -> SimMemOh.t -> Prop)
            (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (smo0: SimMemOh.t): Prop :=
  | fsim_step_step
      (SAFESRC: ~ ms_src.(ModSem.is_call) st_src0 /\ ~ ms_src.(ModSem.is_return) st_src0)
      (STEP: forall st_src1 tr
          (STEPSRC: Step ms_src st_src0 tr st_src1),
          exists i1 st_tgt1 smo1,
            (<<PLUS: DPlus ms_tgt st_tgt0 tr st_tgt1>> \/ <<STAR: DStar ms_tgt st_tgt0 tr st_tgt1 /\ ord i1 i0>>)
            (* /\ <<MCOMPAT: mem_compat st_src1 st_tgt1 smo1>> *)
            /\ <<MLE: SimMemOh.le smo0 smo1>>
(* Note: We require le for mle_preserves_sim_ge, but we cannot require SimMemOh.wf, beacuse of DCEproof *)
            /\ <<UNCH: SimMem.unch midx smo0 smo1>>
            /\ <<FSIM: fsim i1 st_src1 st_tgt1 smo1>>)
      (RECEP: strongly_receptive_at ms_src st_src0)
  | fsim_step_stutter
      i1 st_tgt1 smo1
      (STAR: DPlus ms_tgt st_tgt0 nil st_tgt1 /\ ord i1 i0)
      (MLE: SimMemOh.le smo0 smo1)
      (UNCH: SimMem.unch midx smo0 smo1)
      (BSIM: fsim i1 st_src0 st_tgt1 smo1).

  Inductive bsim_step (bsim: idx -> state ms_src -> state ms_tgt -> SimMemOh.t -> Prop)
            (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (smo0: SimMemOh.t): Prop :=
  | bsim_step_step
      (STEP: forall st_tgt1 tr
          (STEPTGT: Step ms_tgt st_tgt0 tr st_tgt1),
          exists i1 st_src1 smo1,
            (<<PLUS: Plus ms_src st_src0 tr st_src1>> \/ <<STAR: Star ms_src st_src0 tr st_src1 /\ ord i1 i0>>)
            (* /\ <<MCOMPAT: mem_compat st_src1 st_tgt1 smo1>> *)
            /\ <<MLE: SimMemOh.le smo0 smo1>>
            /\ <<UNCH: SimMem.unch midx smo0 smo1>>
            /\ <<BSIM: bsim i1 st_src1 st_tgt1 smo1>>)
  | bsim_step_stutter
      i1 st_src1 smo1
      (STAR: Star ms_src st_src0 nil st_src1 /\ ord i1 i0)
      (MLE: SimMemOh.le smo0 smo1)
      (UNCH: SimMem.unch midx smo0 smo1)
      (BSIM: bsim i1 st_src1 st_tgt0 smo1).

  Inductive _lxsimSR_pre (lxsimSR: idx -> state ms_src -> state ms_tgt -> SimMemOh.t -> Prop)
            (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (smo0: SimMemOh.t): Prop :=
  | lxsimSR_step_forward
      (SU: forall (SU: DUMMY_PROP),
      (* (INTERNALSRC: ms_src.(ModSem.is_internal) st_src0) *)
      (* (INTERNALTGT: ms_tgt.(ModSem.is_internal) st_tgt0) *)
      (* (SAFESRC: ms_src.(ModSem.is_step) st_src0) *)
      <<FSTEP: fsim_step lxsimSR i0 st_src0 st_tgt0 smo0>>
      (* Note: We used coercion on determinate_at. See final_state, which is bot2. *)
      (* sd_determ_at_final becomes nothing, but it is OK. *)
      (* In composed semantics, when it stepped, it must not be final *))

  | lxsimSR_step_backward
      (SU: forall (SU: DUMMY_PROP),
      (* (INTERNALSRC: ms_src.(ModSem.is_internal) st_src0) *)
      (* (INTERNALTGT: ms_tgt.(ModSem.is_internal) st_tgt0) *)
      (* (<<SAFESRC: ~ ms_src.(ModSem.is_call) st_src0 /\ ~ ms_src.(ModSem.is_return) st_src0>>) /\ *)
      (<<BSTEP: forall
          (SAFESRC: safe_modsem ms_src st_src0),
         (<<BSTEP: bsim_step lxsimSR i0 st_src0 st_tgt0 smo0>>)>>) /\
      (<<PROGRESS: forall
           (* (STEPSRC: ms_src.(ModSem.is_step) st_src0) *)
           (STEPSRC: safe_modsem ms_src st_src0),
           (<<STEPTGT: exists tr st_tgt1, Step ms_tgt st_tgt0 tr st_tgt1>>)>>))

  (* | lxsimSR_at_external *)
  (*     rs_arg_src rs_arg_tgt *)
  (*     (MCOMPAT: mem_compat st_src0 st_tgt0 smo0) *)
  (*     m_arg_src m_arg_tgt *)
  (*     (ATSRC: ms_src.(at_external) st_src0 rs_arg_src m_arg_src) *)
  (*     (ATTGT: ms_tgt.(at_external) st_tgt0 rs_arg_tgt m_arg_tgt) *)
  (*     (RSREL: smo0.(SimMemOh.sim_regset) rs_arg_src rs_arg_tgt) *)
  (*     (VALID: SimMemOh.wf smo0) *)
  (*     (AFTER: forall *)
  (*         smo1 rs_ret_src rs_ret_tgt *)
  (*         (MLE: SimMemOh.le (SimMemOh.lift smo0) smo1) *)
  (*         (VALID: SimMemOh.wf smo1) *)
  (*         (RETVREL: smo1.(SimMemOh.sim_regset) rs_ret_src rs_ret_tgt) *)
  (*         st_tgt1 *)
  (*         (AFTERTGT: ms_tgt.(after_external) st_tgt0 rs_arg_tgt rs_ret_tgt smo1.(SimMemOh.tgt) *)
  (*                                                                                st_tgt1) *)
  (*       , *)
  (*         exists i1 st_src1, *)
  (*         (<<AFTERSRC: ms_src.(after_external) st_src0 rs_arg_src rs_ret_src smo1.(SimMemOh.src) *)
  (*                                                                                  st_src1>>) *)
  (*         /\ *)
  (*         (<<LXSIMSR: lxsimSR i1 st_src1 st_tgt1 (SimMemOh.unlift smo0 smo1)>>)) *)

  | lxsimSR_at_external
      (* (MCOMPAT: mem_compat st_src0 st_tgt0 smo0) *)
      (MWF: SimMemOh.wf smo0)
      (* (CALLPROGRESS: forall *)
      (*     rs_arg_src m_arg_src *)
      (*     (ATSRC: ms_src.(at_external) st_src0 rs_arg_src m_arg_src) *)
      (*   , *)
      (*     exists rs_arg_tgt m_arg_tgt, <<ATTGT: ms_tgt.(at_external) st_tgt0 rs_arg_tgt m_arg_tgt>>) *)
      (* (SAFESRC: exists rs_arg_src m_arg_src, <<ATSRC: ms_src.(at_external) st_src0 rs_arg_src m_arg_src>>) *)
      (* (SAFESRC: ms_tgt.(is_call) st_tgt0) *)
      (SAFESRC: ms_src.(is_call) st_src0)
      (* (PROGSRC: ms_src.(is_call) st_src0) *)
      (SU: forall (SU: DUMMY_PROP),
      <<CALLFSIM: forall oh_src0 args_src
          (ATSRC: ms_src.(at_external) st_src0 oh_src0 args_src),
          exists oh_tgt0 args_tgt smo_arg,
            (<<SIMARGS: SimMemOh.sim_args (upcast oh_src0) (upcast oh_tgt0) args_src args_tgt smo_arg>>
            /\ (<<MWF: SimMemOh.wf smo_arg>>)
            /\ (<<MLE: SimMemOh.le smo0 smo_arg>>)
            /\ (<<UNCH: SimMem.unch midx smo0 smo_arg>>)
            /\ (<<ATTGT: ms_tgt.(at_external) st_tgt0 oh_tgt0 args_tgt>>)
            /\ (<<K: forall smo_ret oh_src1 retv_src oh_tgt1 retv_tgt st_src1
                (MLE: SimMemOh.lepriv smo_arg smo_ret)
                (MWF: SimMemOh.wf smo_ret)
                (SIMRETV: SimMemOh.sim_retv (upcast oh_src1) (upcast oh_tgt1) retv_src retv_tgt smo_ret)
                (AFTERSRC: ms_src.(after_external) st_src0 oh_src1 retv_src st_src1),
                exists st_tgt1 smo_after i1,
                  (<<AFTERTGT: ms_tgt.(after_external) st_tgt0 oh_tgt1 retv_tgt st_tgt1>>) /\
                  (<<MLEPUB: SimMemOh.le smo0 smo_after>>) /\
                  (<<MLEPRIV: SimMemOh.lepriv smo_ret smo_after>>) /\
                  (<<UNCH: SimMem.unch midx smo_ret smo_after>>) /\
                  (<<LXSIMSR: lxsimSR i1 st_src1 st_tgt1 smo_after>>)>>))>>)

  | lxsimSR_final
      smo_ret oh_src oh_tgt retv_src retv_tgt
      (MLE: SimMemOh.le smo0 smo_ret)
      (UNCH: SimMem.unch midx smo0 smo_ret)
      (MWF: SimMemOh.wf smo_ret)
      (* (PROGRESS: ms_tgt.(is_return) rs_init_tgt st_tgt0) *)
      (* (RETBSIM: forall           *)
      (*     rs_ret_tgt m_ret_tgt *)
      (*     (FINALTGT: ms_tgt.(final_frame) rs_init_tgt st_tgt0 rs_ret_tgt m_ret_tgt) *)
      (*   , *)
      (*     exists rs_ret_src m_ret_src, *)
      (*       (<<RSREL: smo0.(SimMemOh.sim_regset) rs_ret_src rs_ret_tgt>>) *)
      (*       /\ (<<FINALSRC: ms_src.(final_frame) rs_init_src st_src0 rs_ret_src m_ret_src>>)) *)
      (FINALSRC: ms_src.(final_frame) st_src0 oh_src retv_src)
      (FINALTGT: ms_tgt.(final_frame) st_tgt0 oh_tgt retv_tgt)
      (SIMRETV: SimMemOh.sim_retv (upcast oh_src) (upcast oh_tgt) retv_src retv_tgt smo_ret).

      (* Note: Actually, final_frame can be defined as a function. *)

      (* (FINALSRC: ms_src.(final_frame) rs_init_src st_src0 rs_ret_src m_ret_src) *)
      (* (FINALTGT: ms_tgt.(final_frame) rs_init_tgt st_tgt0 rs_ret_tgt m_ret_tgt) *)

  Definition _lxsimSR (lxsimSR: idx -> state ms_src -> state ms_tgt -> SimMemOh.t -> Prop)
             (i0: idx) (st_src0: ms_src.(state)) (st_tgt0: ms_tgt.(state)) (smo0: SimMemOh.t): Prop :=
    (forall (SUSTAR: forall st_src1 tr (STAR: Star ms_src st_src0 tr st_src1), sound_states st_src1),
        <<LXSIM: _lxsimSR_pre lxsimSR i0 st_src0 st_tgt0 smo0>>).

  Definition lxsimSR: _ -> _ -> _ -> _ -> Prop := paco4 _lxsimSR bot4.

  Lemma lxsimSR_mon: monotone4 _lxsimSR.
  Proof.
    repeat intro. rr in IN. hexploit1 IN; eauto. inv IN; eauto.
    - econs 1; ss. ii. spc SU. des. inv SU.
      + econs 1; eauto. i; des_safe. exploit STEP; eauto. i; des_safe. esplits; eauto.
      + econs 2; eauto.
    - econs 2; ss. i. exploit SU; eauto. i; des.
      esplits; eauto. i. hexploit BSTEP; eauto. i. inv H.
      + econs 1; eauto. i; des_safe. exploit STEP; eauto. i; des_safe. esplits; eauto.
      + econs 2; eauto.
    - econs 3; eauto. ii; ss. exploit SU; eauto. i; des.
      esplits; eauto. ii. exploit K; eauto. i; des. esplits; eauto.
    - econs 4; eauto.
  Qed.

End SIMMODSEM.

Hint Unfold lxsimSR.
Hint Resolve lxsimSR_mon: paco.


Module ModSemPair.
Include SimModSem.ModSemPair.
Section MODSEMPAIR.
Context {SM: SimMem.class} {SS: SimSymb.class SM} {SU: Sound.class}.


  Inductive simSR (msp: t): Prop :=
  | simSR_intro
      (* (SIMSKENV: sim_skenv msp msp.(smo)) *)
      sidx sound_states sound_state_ex
      (MIDX: SimMemOh.midx (class := msp.(SMO)) = msp.(src).(midx))
      (MIDX: msp.(src).(midx) = msp.(tgt).(midx))
      (MIDXNONE: SimMemOh.midx (class := msp.(SMO)) = None -> msp.(SMO) = SimMemOh_default _)
      (PRSV: local_preservation msp.(src) sound_state_ex)
      (PRSVNOGR: forall (si: sidx), local_preservation_noguarantee msp.(src) (sound_states si))
      (INITOH: forall
          sm
          (SIMSKENV: sim_skenv msp sm)
          (WF: SimMem.wf sm)
        ,
          exists (smo: SimMemOh.t (class := msp.(SMO))),
            (<<WF: SimMemOh.wf smo>>) /\
            (<<SMEQ: smo.(SimMemOh.sm) = sm>>) /\
            (<<OHSRC: smo.(SimMemOh.oh_src) = upcast msp.(src).(initial_owned_heap)>>) /\
            (<<OHTGT: smo.(SimMemOh.oh_tgt) = upcast msp.(tgt).(initial_owned_heap)>>))
      (SIM: forall
          (smo_arg: SimMemOh.t (class := msp.(SMO)))
          oh_src args_src oh_tgt args_tgt
          sg_init_src sg_init_tgt
          (FINDFSRC: (Genv.find_funct msp.(src).(ModSem.skenv)) (Args.get_fptr args_src) =
                     Some (Internal sg_init_src))
          (FINDFTGT: (Genv.find_funct msp.(tgt).(ModSem.skenv)) (Args.get_fptr args_tgt) =
                     Some (Internal sg_init_tgt))
          (SIMARGS: SimMemOh.sim_args (upcast oh_src) (upcast oh_tgt) args_src args_tgt smo_arg)
          (SIMSKENV: sim_skenv msp smo_arg)
          (MFUTURE: SimMem.future msp.(sm) smo_arg)
          (MWF: SimMemOh.wf smo_arg),
          (<<INITBSIM: forall st_init_tgt
              (INITTGT: msp.(tgt).(initial_frame) oh_tgt args_tgt st_init_tgt)
              (SAFESRC: exists _st_init_src, msp.(src).(initial_frame) oh_src args_src _st_init_src),
              exists st_init_src smo_init idx_init,
                (<<MLE: SimMemOh.le smo_arg smo_init>>) /\
                (<<UNCH: SimMem.unch msp.(src).(midx) smo_arg smo_init>>) /\
                (<<INITSRC: msp.(src).(initial_frame) oh_src args_src st_init_src>>) /\
                (<<SIM: lxsimSR msp.(src) msp.(tgt) (fun st => forall si, exists su m_init, (sound_states si) su m_init st)
                                                  idx_init st_init_src st_init_tgt smo_init>>)>>) /\
          (<<INITPROGRESS: forall
              (SAFESRC: exists st_init_src, msp.(src).(initial_frame) oh_src args_src st_init_src),
              exists st_init_tgt,
                (<<INITTGT: msp.(tgt).(initial_frame) oh_tgt args_tgt st_init_tgt>>)>>)).

End MODSEMPAIR.
End ModSemPair.

Hint Constructors ModSemPair.sim_skenv.

Lemma atomic_unlift_safe_modsem
      ms_src st_src0
      (SAFE: safe_modsem (Atomic.trans ms_src) ([], st_src0))
      (WBT: well_behaved_traces ms_src):
  <<SAFE: safe_modsem ms_src st_src0>>.
Proof.
  ii. exploit SAFE; eauto.
  { instantiate (1:= (_, _)). eapply ModSem.Atomic.atomic_lift_star; eauto. }
  i; des.
  - left. rr in EVCALL. des. rr. inv EVCALL. ss. esplits; eauto.
  - right. left. rr in EVRET. des. rr. inv EVRET. ss. esplits; eauto.
  - right. right. rr in EVSTEP. inv EVSTEP; esplits; eauto.
Qed.

Section FACTORSOURCE.

  Context `{SMO: SimMemOh.class} {SS: SimSymb.class _} {SU: Sound.class}.
  Variable ms_src ms_tgt: ModSem.t.
  Variable ss: SimSymb.t.
  Hypothesis WBT: well_behaved_traces ms_src.
  Hypothesis SINGLE: single_events ms_tgt.

  Section LXSIM.

    Variable sound_states: state ms_src -> Prop.

    Inductive ffs_match: idx -> (trace * state ms_src) -> state ms_tgt -> SimMemOh.t -> Prop :=
    | ffs_match_at
        idx0 st_src0 st_tgt0 smo0
        (MATCH: lxsimSR ms_src ms_tgt sound_states idx0 st_src0 st_tgt0 smo0):
        ffs_match idx0 ([], st_src0) st_tgt0 smo0
    | ffs_match_buffer
        idx0 st_src0 ev tr st_tgt0 st_tgt1 smo0
        (* (SSR: strongly_receptive_at ms_src st_src0) *)
        (PLUS: DPlus ms_tgt st_tgt0 (ev :: tr) st_tgt1)
        (MATCH: lxsimSR ms_src ms_tgt sound_states idx0 st_src0 st_tgt1 smo0):
        ffs_match idx0 (ev :: tr, st_src0) st_tgt0 smo0.

    Lemma factor_lxsim_source: forall idx0 st_src0 tr st_tgt0 smo0
        (SIM: ffs_match idx0 (tr, st_src0) st_tgt0 smo0),
        <<SIM: SimModSem.lxsim (Atomic.trans ms_src) ms_tgt (fun st => sound_states (snd st)) idx0 (tr, st_src0) st_tgt0 smo0>>.
    Proof.
      clear_tac. unfold NW. pcofix CIH. i. pfold. inv SIM; cycle 1.
      (* exploit atomic_receptive; eauto. intro RECEP. *)
      { econs; eauto. ss. i. econs; eauto; cycle 2.
        { eapply atomic_receptive_at_nonnil; eauto. }
        { split; intro T; rr in T; des; inv T; ss. }
        i. inv STEPSRC. ss. des. exploit Pstar_non_E0_split'_strong; swap 1 2; eauto.
        { eapply plus_star; eauto. }
        intro P; ss. des_safe. des.
        - esplits; eauto; try refl.
          + pclearbot. right. eapply CIH; eauto. destruct tr0; ss. econs; eauto.
        - clarify. esplits; eauto; try refl.
          + pclearbot. right. eapply CIH; eauto. econs; eauto.
      }
      punfold MATCH. rr in MATCH. ii. hexploit1 MATCH; eauto.
      { ii. exploit SUSTAR. { instantiate (1:= (_, _)). eapply ModSem.Atomic.atomic_lift_star; eauto. } ii; ss. }
      inv MATCH.
      - econs 1. i. exploit SU; eauto. i; des_safe.
        rename H into FSTEP. clear - SINGLE CIH FSTEP. inv FSTEP.
        + econs 1; eauto; cycle 2.
          { eapply atomic_receptive_at; eauto. }
          { split; intro T; rr in T; des; ss.
            - apply SAFESRC. rr. inv T. esplits; eauto.
            - apply SAFESRC0. rr. inv T. esplits; eauto. }
          i. inv STEPSRC; ss.
          * exploit STEP; eauto. i; des_safe. esplits; eauto.
            pclearbot. right. eapply CIH; eauto. econs; eauto.
          * exploit STEP; eauto. i; des_safe. des.
            { exploit Pstar_non_E0_split'_strong; swap 1 2; eauto.
              { eapply plus_star; eauto. }
              intro P; ss. des_safe. des; clarify.
              - destruct tr0; ss. esplits; eauto. pclearbot. right. eapply CIH; eauto. econs; eauto.
              - esplits; eauto. pclearbot. right. eapply CIH; eauto. econs; eauto.
            }
            { exploit Pstar_non_E0_split'_strong; swap 1 2; eauto. intro P; ss. des_safe. des; clarify.
              - destruct tr0; ss. esplits; eauto. pclearbot. right. eapply CIH; eauto. econs; eauto.
              - esplits; eauto. pclearbot. right. eapply CIH; eauto. econs; eauto.
            }
        + des. econs 2; eauto. pclearbot. right. eapply CIH; eauto. econs; eauto.
      - econs 2. i. exploit SU; eauto. i; des. esplits; eauto.
        + (* bsim *)
          clear - WBT SINGLE CIH BSTEP PROGRESS. i. hexploit BSTEP; eauto.
          { eapply atomic_unlift_safe_modsem; eauto. }
          clear BSTEP; intro BSTEP. inv BSTEP.
          * econs 1; eauto; cycle 1.
            { (* progress *) i. exploit PROGRESS; eauto. eapply atomic_unlift_safe_modsem; eauto. }
            i.
            exploit STEP; eauto. i; des_safe. esplits; eauto.
            { des.
              - left. instantiate (1:= (_, _)). eapply plus_atomic_plus; eauto.
              - right. split; eauto. eapply star_atomic_star; eauto.
            }
            pclearbot. right. eapply CIH; eauto. econs; eauto.
          * des. econs 2; eauto.
            { split; eauto. instantiate (1:= (_, _)). eapply star_atomic_star; et. }
            pclearbot. right. eapply CIH; eauto. econs; eauto.
      - rr in SAFESRC. des. econs 3; eauto.
        { rr. esplits; eauto. econs; eauto. }
        ii. exploit SU; eauto. i; des. inv ATSRC. ss. determ_tac at_external_dtm.
        esplits; eauto. i. inv AFTERSRC. des; ss. destruct st_src1; ss. clarify. clear_tac.
        exploit K; eauto. i; des. esplits; eauto. pclearbot. right. eapply CIH; eauto. econs; eauto.
      - econs 4; eauto. rr. esplits; eauto.
    Qed.

  End LXSIM.

  Variable smo: SimMemOh.t.

  Theorem factor_simmodsem_source
          (SIM: ModSemPair.simSR (ModSemPair.mk ms_src ms_tgt ss smo _)):
      ModSemPair.sim (ModSemPair.mk (ModSem.Atomic.trans ms_src) ms_tgt ss smo _).
  Proof.
    inv SIM. ss. econs; eauto; ss.
    { instantiate (1:= fun su m st_src => sound_state_ex su m (snd st_src)). ss.
      i. specialize (PRSV). inv PRSV. econs; ss; eauto.
      - ii. exploit INIT; eauto. rr in INIT0. des. ss; et.
      - ii. inv STEP0; ss.
        { exploit STEP; eauto.
          { des. split; intro T; rr in T; des.
            - contradict SAFE. rr. esplits; eauto. econs; eauto.
            - contradict SAFE0. rr. esplits; eauto. econs; eauto.
          }
        }
        { exploit STEP; eauto.
          { des. split; intro T; rr in T; des.
            - contradict SAFE. rr. esplits; eauto. econs; eauto.
            - contradict SAFE0. rr. esplits; eauto. econs; eauto.
          }
        }
      - i. rr in AT. des. destruct st0; ss. clarify.
        exploit CALL; eauto. i; des. esplits; eauto.
        i. exploit K; eauto. rr in AFTER. des. ss; et.
      - i. exploit RET; eauto. rr in FINAL. des. ss; et.
    }
    { i. instantiate (1:= fun si su m st_src => sound_states si su m (snd st_src)). ss.
      i. specialize (PRSVNOGR si).
      inv PRSVNOGR. econs; ss; eauto.
      - ii. exploit INIT; eauto. rr in INIT0. des. ss; et.
      - ii. inv STEP0; ss.
        { exploit STEP; eauto.
          { des. split; intro T; rr in T; des.
            - contradict SAFE. rr. esplits; eauto. econs; eauto.
            - contradict SAFE0. rr. esplits; eauto. econs; eauto.
          }
        }
        { exploit STEP; eauto.
          { des. split; intro T; rr in T; des.
            - contradict SAFE. rr. esplits; eauto. econs; eauto.
            - contradict SAFE0. rr. esplits; eauto. econs; eauto.
          }
        }
      - i. rr in AT. des. destruct st0; ss. clarify.
        exploit CALL; eauto. i; des. esplits; eauto.
        i. exploit K; eauto. rr in AFTER. des. ss; et.
    }
    { i. exploit INITOH; et. inv SIMSKENV. econs; ss; et. }
    i. exploit SIM0; eauto.
    { inv SIMSKENV. ss. econs; eauto. }
    i; des.
    split; ss.
    - ii. des. exploit INITBSIM; eauto.
      { rr in SAFESRC. des. esplits; eauto. }
      i; des. clears _st_init_src. clear_tac. esplits; eauto.
      { instantiate (1:= (_, _)). econs; ss; eauto. }
      eapply factor_lxsim_source with (sound_states := fun st => forall si, exists su m_init, sound_states si su m_init st). econs; eauto.
    - ii. des. exploit INITPROGRESS; eauto. rr in SAFESRC. des. esplits; eauto.
  Qed.

End FACTORSOURCE.
