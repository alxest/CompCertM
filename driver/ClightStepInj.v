Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import Simulation Ctypes Cop Ctyping Csyntax Clight.
Require SimMemId SimMemExt SimMemInj.
Require SoundTop UnreachC.
Require SimSymbId SimSymbDrop.
Require Import CoqlibC.
Require Import ValuesC.
Require Import LinkingC.
Require Import MapsC.
Require Import AxiomsC.
Require Import Ord.
Require Import MemoryC.
Require Import SmallstepC.
Require Import Events.
Require Import Preservation.
Require Import Integers.
Require Import LocationsC Conventions.

Require Import MatchSimModSem.
Require Import mktac.
Require Import IntegersC.
Require Import IdSimExtra.

Set Implicit Arguments.

Local Opaque Z.mul Z.add Z.sub Z.div.

(* copied from ClightC *)
Definition get_mem (st: state): mem :=
  match st with
  | State _ _ _ _ _ m0 => m0
  | Callstate _ _ _ _ m0 => m0
  | Returnstate _ _ m0 => m0
  end
.

(* TODO : copied from AsmStepInj. move it to IdSimExtra *)
Section MOVETOIDSIMEXTRA.
  Lemma mem_store_readonly
        chunk m0 m1 b ofs v
        (STORE: Mem.store chunk m0 b ofs v = Some m1)
  :
    Mem.unchanged_on (loc_not_writable m0) m0 m1.
  Proof.
    eapply Mem.unchanged_on_implies; try eapply Mem.store_unchanged_on; eauto.
    ii. apply Mem.store_valid_access_3 in STORE. apply H0.
    apply Mem.perm_cur_max. eapply STORE; eauto.
  Qed.

  Lemma mem_free_readonly
        m0 m1 b lo hi
        (STORE: Mem.free m0 b lo hi = Some m1)
    :
      Mem.unchanged_on (loc_not_writable m0) m0 m1.
  Proof.
    eapply Mem.unchanged_on_implies; try eapply Mem.free_unchanged_on; eauto.
    ii. apply H0.
    apply Mem.perm_cur_max. eapply Mem.perm_implies.
    - eapply Mem.free_range_perm; eauto.
    - econs.
  Qed.

  Lemma mem_readonly_trans
        m0 m1 m2
        (UNCH0: Mem.unchanged_on (loc_not_writable m0) m0 m1)
        (UNCH1: Mem.unchanged_on (loc_not_writable m1) m1 m2)
    :
      Mem.unchanged_on (loc_not_writable m0) m0 m2.
  Proof.
    inv UNCH0. inv UNCH1.
    econs.
    - etrans; eauto.
    - ii. exploit unchanged_on_perm; eauto. i. etrans; eauto.
      eapply unchanged_on_perm0; eauto.
      + ii. eapply unchanged_on_perm in H2; eauto.
      + unfold Mem.valid_block in *. eapply Plt_Ple_trans; eauto.
    - ii. exploit unchanged_on_contents; eauto. i. etrans; try apply H1.
      eapply unchanged_on_contents0; eauto.
      + ii. eapply unchanged_on_perm in H2; eauto.
        eapply Mem.perm_valid_block; eauto.
      + eapply unchanged_on_perm; eauto.
        eapply Mem.perm_valid_block; eauto.
  Qed.
End MOVETOIDSIMEXTRA.

Lemma mem_free_list_readonly
      m0 m1 ls
      (STORE: Mem.free_list m0 ls = Some m1)
  :
    Mem.unchanged_on (loc_not_writable m0) m0 m1.
Proof.
  revert m0 m1 STORE. induction ls; ss; i.
  - clarify. refl.
  - des_ifs. eapply mem_readonly_trans; eauto.
    eapply mem_free_readonly; eauto.
Qed.

Lemma clight_step_readonly se ge st0 st1 tr
      (STEP: step se ge (function_entry2 ge) st0 tr st1)
  :
    Mem.unchanged_on (loc_not_writable st0.(get_mem)) st0.(get_mem) st1.(get_mem).
Proof.
  inv STEP; ss; try refl.
  - inv H2.
    + unfold Mem.storev in *. eapply mem_store_readonly; eauto.
    + eapply Mem.storebytes_unchanged_on; eauto. ii.
      unfold loc_not_writable in *. eapply H9. eapply Mem.perm_cur.
      eapply Mem.storebytes_range_perm; eauto.
  - eapply external_call_readonly; eauto.
  - eapply mem_free_list_readonly; eauto.
  - eapply mem_free_list_readonly; eauto.
  - eapply mem_free_list_readonly; eauto.
  - inv H. eapply alloc_variables_unchanged_on; eauto.
  - eapply external_call_readonly; eauto.
Qed.


Definition match_env (j: meminj) (env_src env_tgt: env) :=
  forall id,
    (<<MAPPED: exists blk_src blk_tgt ty,
        (<<INJ: j blk_src = Some (blk_tgt, 0)>>) /\
        (<<BLKSRC: env_src ! id = Some (blk_src, ty)>>) /\
        (<<BLKTGT: env_tgt ! id = Some (blk_tgt, ty)>>)>>) \/
    (<<NOTMAPPED:
       (<<BLKSRC: env_src ! id = None>>) /\
       (<<BLKTGT: env_tgt ! id = None>>)>>)
.

Definition match_temp_env (j: meminj) (tenv_src tenv_tgt: temp_env) :=
  forall id,
    option_rel (Val.inject j) (tenv_src ! id) (tenv_tgt ! id).

Inductive match_cont (j: meminj): cont -> cont -> Prop :=
| match_Kstop:
    match_cont j Kstop Kstop
| match_Kseq
    stmt K_src K_tgt
    (CONT: match_cont j K_src K_tgt)
  :
    match_cont j (Kseq stmt K_src) (Kseq stmt K_tgt)
| match_Kloop1
    stmt0 stmt1 K_src K_tgt
    (CONT: match_cont j K_src K_tgt)
  :
    match_cont j (Kloop1 stmt0 stmt1 K_src) (Kloop1 stmt0 stmt1 K_tgt)
| match_Kloop2
    stmt0 stmt1 K_src K_tgt
    (CONT: match_cont j K_src K_tgt)
  :
    match_cont j (Kloop2 stmt0 stmt1 K_src) (Kloop2 stmt0 stmt1 K_tgt)
| match_Kswitch
    K_src K_tgt
    (CONT: match_cont j K_src K_tgt)
  :
    match_cont j (Kswitch K_src) (Kswitch K_tgt)
| match_Kcall
    id fn
    env_src env_tgt
    tenv_src tenv_tgt
    K_src K_tgt
    (ENV: match_env j env_src env_tgt)
    (TENV: match_temp_env j tenv_src tenv_tgt)
    (CONT: match_cont j K_src K_tgt)
  :
    match_cont j (Kcall id fn env_src tenv_src K_src) (Kcall id fn env_tgt tenv_tgt K_tgt)
.

Inductive match_states_clight_internal:
  state -> state -> meminj -> mem -> mem -> Prop :=
| match_State
    fn stmt K_src K_tgt env_src env_tgt tenv_src tenv_tgt m_src m_tgt j
    (ENV: match_env j env_src env_tgt)
    (TENV: match_temp_env j tenv_src tenv_tgt)
    (CONT: match_cont j K_src K_tgt)
  :
    match_states_clight_internal
      (State fn stmt K_src env_src tenv_src m_src)
      (State fn stmt K_tgt env_tgt tenv_tgt m_tgt)
      j m_src m_tgt
| match_Callstate
    fptr_src fptr_tgt ty args_src args_tgt K_src K_tgt m_src m_tgt j
    (INJ: Val.inject j fptr_src fptr_tgt)
    (VALS: Val.inject_list j args_src args_tgt)
    (CONT: match_cont j K_src K_tgt)
  :
    match_states_clight_internal
      (Callstate fptr_src ty args_src K_src m_src)
      (Callstate fptr_tgt ty args_tgt K_tgt m_tgt)
      j m_src m_tgt
| match_Returnstate
    retv_src retv_tgt K_src K_tgt m_src m_tgt j
    (INJ: Val.inject j retv_src retv_tgt)
    (CONT: match_cont j K_src K_tgt)
  :
    match_states_clight_internal
      (Returnstate retv_src K_src m_src)
      (Returnstate retv_tgt K_tgt m_tgt)
      j m_src m_tgt
.

Inductive match_states_clight (sm_arg: SimMemInj.t')
  : unit -> state -> state -> SimMemInj.t' -> Prop :=
| match_states_clight_intro
    st_src st_tgt j m_src m_tgt sm0
    (MWFSRC: m_src = sm0.(SimMemInj.src))
    (MWFTGT: m_tgt = sm0.(SimMemInj.tgt))
    (MWFINJ: j = sm0.(SimMemInj.inj))
    (MATCHST: match_states_clight_internal st_src st_tgt j m_src m_tgt)
    (MWF: SimMemInj.wf' sm0)
  :
    match_states_clight
      sm_arg tt st_src st_tgt sm0
.

Section CLIGHTINJ.

  Variable se_src se_tgt: Senv.t.
  Variable ge_src ge_tgt: genv.
  Hypothesis CENV: genv_cenv ge_src = genv_cenv ge_tgt.
  (* TODO: injection condition of env *)

  Definition function_entry_inject
             (function_entry: genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)
    :=
      forall
        fn vs_src vs_tgt sm0 env_src tenv_src m_src1
        (MWF: SimMemInj.wf' sm0)
        (VALS: Val.inject_list sm0.(SimMemInj.inj) vs_src vs_tgt)
        (ENTRY: function_entry ge_src fn vs_src sm0.(SimMemInj.src) env_src tenv_src m_src1),
      exists env_tgt tenv_tgt sm1,
        (<<MEMSRC: SimMemInj.src sm1 = m_src1>>) /\
        (<<MWF: SimMemInj.wf' sm1>>) /\
        (<<ENV: match_env sm1.(SimMemInj.inj) env_src env_tgt>>) /\
        (<<TENV: match_temp_env sm1.(SimMemInj.inj) tenv_src tenv_tgt>>) /\
        (<<MLE: SimMemInj.le' sm0 sm1>>) /\
        (<<ENTRY: function_entry ge_tgt fn vs_tgt sm0.(SimMemInj.tgt) env_tgt tenv_tgt sm1.(SimMemInj.tgt)>>).

  Lemma alloc_variables_inject sm0 idl e_src0 e_tgt0 e_src1 m_src1
        (ALLOC: alloc_variables ge_src e_src0 (SimMemInj.src sm0) idl e_src1 m_src1)
        (ENV: match_env (SimMemInj.inj sm0) e_src0 e_tgt0)
        (MWF: SimMemInj.wf' sm0)
    :
      exists e_tgt1 sm1,
        (<<MEMSRC: SimMemInj.src sm1 = m_src1>>) /\
        (<<MWF: SimMemInj.wf' sm1>>) /\
        (<<MLE: SimMemInj.le' sm0 sm1>>) /\
        (<<ENV: match_env (SimMemInj.inj sm1) e_src1 e_tgt1>>) /\
        (<<ALLOC: alloc_variables ge_tgt e_tgt0 (SimMemInj.tgt sm0) idl e_tgt1 (SimMemInj.tgt sm1)>>).
  Proof.
    revert sm0 MWF e_src0 e_tgt0 e_src1 m_src1 ENV ALLOC. induction idl.
    - i. inv ALLOC. esplits; eauto.
      + refl.
      + econs.
    - i. inv ALLOC.
      exploit SimMemInj.alloc_parallel; eauto; try refl. i. des. clarify.
      exploit IHidl; eauto.
      { instantiate (1:=PTree.set id (blk_tgt, ty) e_tgt0).
        ii. repeat rewrite PTree.gsspec. des_ifs.
        - left. esplits; eauto.
        - destruct (ENV id0).
          + des. left. inv MLE. esplits; cycle 1; eauto.
          + right. eauto. }
      i. des. clarify.
      esplits; eauto.
      + etrans; eauto.
      + econs; eauto.
        rewrite <- CENV. auto.
  Qed.

  (* TODO: move it to MemoryC *)
  Lemma storebytes_mapped
        sm0 b tb ofs bytes1 bytes2 m_src delta
        (MWF : SimMemInj.wf' sm0)
        (STRSRC: Mem.storebytes (SimMemInj.src sm0) b ofs bytes1 = Some m_src)
        (SIMBLK: (SimMemInj.inj sm0) b = Some (tb, delta))
        (BYTESINJ: list_forall2 (memval_inject (SimMemInj.inj sm0)) bytes1 bytes2)
    (* (SIMADDR: Val.inject (SimMemInj.inj sm0) (Vptr b ofs) (Vptr tb tofs)) *)
    :
      exists sm1,
        (<<MSRC: (SimMemInj.src sm1) = m_src>>)
        /\ (<<MINJ: (SimMemInj.inj sm1) = (SimMemInj.inj sm0)>>)
        /\ (<<STRTGT: Mem.storebytes (SimMemInj.tgt sm0) tb (ofs + delta) bytes2 = Some (SimMemInj.tgt sm1)>>)
        /\ (<<MWF: SimMemInj.wf' sm1>>)
        /\ (<<MLE: SimMemInj.le' sm0 sm1>>)
  .
  Proof.
    (* inv SIMADDR. *)
    exploit Mem.storebytes_mapped_inject; eauto.
    { inv MWF. eauto. }
    i. des.
    inv MWF.
    eexists (SimMemInj.mk _ _ _ _ _ _ _ _ _).
    esplits; ss; eauto; cycle 1.
    - econs; ss; eauto.
      + eapply Mem.storebytes_unchanged_on; eauto.
        ii. apply SRCEXT in H2. red in H2. des. red in H2. clarify.
      + eapply Mem.storebytes_unchanged_on; eauto.
        ii. apply TGTEXT in H2. red in H2. des. red in H2.
        eapply H2; eauto. clear - BYTESINJ STRSRC H1 H4.
        eapply Mem.storebytes_range_perm in STRSRC.
        assert (Datatypes.length bytes2 = Datatypes.length bytes1).
        { exploit list_forall2_length; eauto. }
        rewrite H in *.
        assert (ofs <= i - delta) by nia.
        assert (i - delta < ofs + Z.of_nat (Datatypes.length bytes1)) by nia.
        unfold Mem.range_perm in STRSRC.
        specialize (STRSRC (i - delta)). exploit STRSRC. nia.
        i. eapply Mem.perm_cur_max. eapply Mem.perm_implies; eauto.
        eapply perm_any_N.
      + eapply SimMemInj.frozen_refl.
      + eapply SimMemInj.frozen_refl.
      + ii. eapply Mem.perm_storebytes_2; eauto.
      + ii. eapply Mem.perm_storebytes_2; eauto.
    - econs; ss; eauto.
      + etransitivity; eauto. unfold SimMemInj.src_private. ss. ii; des. esplits; eauto.
        unfold SimMemInj.valid_blocks, Mem.valid_block in *.
        erewrite Mem.nextblock_storebytes; eauto.
      + etransitivity; eauto. unfold SimMemInj.tgt_private. ss. ii; des. esplits; eauto.
        { ii. eapply PR; eauto. eapply Mem.perm_storebytes_2; eauto. }
        unfold SimMemInj.valid_blocks, Mem.valid_block in *.
        erewrite Mem.nextblock_storebytes; eauto.
      + etransitivity; eauto. erewrite <- Mem.nextblock_storebytes; eauto. refl.
      + etransitivity; eauto. erewrite <- Mem.nextblock_storebytes; eauto. refl.
  Qed.

  Lemma assign_loc_inject ce ty sm0 blk_src blk_tgt ofs_src ofs_tgt v_src v_tgt m_src1
        (ASSIGN: assign_loc ce ty sm0.(SimMemInj.src) blk_src ofs_src v_src m_src1)
        (INJ: Val.inject sm0.(SimMemInj.inj) (Vptr blk_src ofs_src) (Vptr blk_tgt ofs_tgt))
        (VAL: Val.inject sm0.(SimMemInj.inj) v_src v_tgt)
        (MWF: SimMemInj.wf' sm0)
    :
      exists sm1,
        (<<ASSIGN: assign_loc ce ty sm0.(SimMemInj.tgt) blk_tgt ofs_tgt v_tgt sm1.(SimMemInj.tgt)>>) /\
        (<<MEMSRC: SimMemInj.src sm1 = m_src1>>) /\
        (<<MWF: SimMemInj.wf' sm1>>) /\
        (<<MLE: SimMemInj.le' sm0 sm1>>).
  Proof.
    cinv MWF. inv ASSIGN.
    - exploit SimMemInj.storev_mapped; eauto. i. des. clarify.
      esplits; eauto. econs 1; eauto.
    - destruct (zeq (sizeof ce ty) 0).
      + cinv VAL. cinv INJ.
        assert (bytes = nil).
        { exploit (Mem.loadbytes_empty (SimMemInj.src sm0) b' (Ptrofs.unsigned ofs') (sizeof ce ty)).
          omega. congruence. } subst.
        destruct (Mem.range_perm_storebytes (SimMemInj.tgt sm0) blk_tgt (Ptrofs.unsigned (Ptrofs.add ofs_src (Ptrofs.repr delta0))) nil)
          as [tm' SB].
        { simpl. red; intros; omegaContradiction. }
        eexists (SimMemInj.mk _ tm' _ _ _ _ _ _ _); ss. esplits; cycle 3; eauto.
        * econs; ss; eauto.
          { eapply Mem.storebytes_unchanged_on; eauto.
            i. ss. omega. }
          { eapply Mem.storebytes_unchanged_on; eauto.
            i. ss. omega. }
          { econs. i. clear - NEW. des. clarify. }
          { econs. i. clear - NEW. des. clarify. }
          { ii. eapply Mem.perm_storebytes_2; eauto. }
          { ii. eapply Mem.perm_storebytes_2; eauto. }
       * econs 2; eauto.
          { intros; omegaContradiction. }
          { intros; omegaContradiction. }
          { rewrite e; right; omega. }
          { apply Mem.loadbytes_empty. omega. }
        * inv MWF. econs; ss; eauto.
          { eapply Mem.storebytes_empty_inject; eauto. }
          { unfold SimMemInj.src_private, SimMemInj.valid_blocks, Mem.valid_block. ss.
            erewrite Mem.nextblock_storebytes; eauto. }
          { ii. exploit TGTEXT0; eauto.
            unfold SimMemInj.tgt_private, SimMemInj.valid_blocks, Mem.valid_block, loc_out_of_reach. ss.
            erewrite (@Mem.nextblock_storebytes _ _ _ _ _ SB). i.
            des_safe. split; eauto. ii.
            eapply H5; eauto. eapply Mem.perm_storebytes_2; eauto. }
          { erewrite Mem.nextblock_storebytes; eauto. }
          { erewrite Mem.nextblock_storebytes; eauto. }
      + assert (SZPOS: sizeof ce ty > 0).
        { generalize (sizeof_pos ce ty); omega. }
        cinv VAL. cinv INJ.
        assert (RPSRC: Mem.range_perm (SimMemInj.src sm0) b' (Ptrofs.unsigned ofs') (Ptrofs.unsigned ofs' + sizeof ce ty) Cur Nonempty).
        { eapply Mem.range_perm_implies.
          - eapply Mem.loadbytes_range_perm; eauto.
          - econs. }
        assert (RPDST: Mem.range_perm (SimMemInj.src sm0) blk_src (Ptrofs.unsigned ofs_src) (Ptrofs.unsigned ofs_src + sizeof ce ty) Cur Nonempty).
        { replace (sizeof ce ty) with (Z.of_nat (List.length bytes)).
          - eapply Mem.range_perm_implies.
            + eapply Mem.storebytes_range_perm; eauto.
            + econs.
          - exploit Mem.loadbytes_length; try apply H3; eauto. intros LEN.
            rewrite LEN. apply nat_of_Z_eq. omega. }
        assert (PSRC: Mem.perm (SimMemInj.src sm0) b' (Ptrofs.unsigned ofs') Cur Nonempty).
        { apply RPSRC. omega. }
        assert (PDST: Mem.perm (SimMemInj.src sm0) blk_src (Ptrofs.unsigned ofs_src) Cur Nonempty).
        { apply RPDST. omega. }
        exploit Mem.address_inject; try apply PSRC; eauto. intros EQ1.
        exploit Mem.address_inject; try apply PDST; eauto. intros EQ2.
        exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
        exploit storebytes_mapped; eauto. i. des_safe.
        exists sm1. splits; auto. econs 2; try rewrite EQ1; try rewrite EQ2; eauto.
        * intros; eapply Mem.aligned_area_inject with (m := SimMemInj.src sm0); eauto.
          { apply alignof_blockcopy_1248. }
          { apply sizeof_alignof_blockcopy_compat. }
        * intros; eapply Mem.aligned_area_inject with (m := SimMemInj.src sm0); eauto.
          { apply alignof_blockcopy_1248. }
          { apply sizeof_alignof_blockcopy_compat. }
        *  eapply Mem.disjoint_or_equal_inject with (m := SimMemInj.src sm0); eauto.
           { apply Mem.range_perm_max with Cur; auto. }
           { apply Mem.range_perm_max with Cur; auto. }
  Qed.

  Lemma call_cont_match j K_src K_tgt
        (MATCH: match_cont j K_src K_tgt)
    :
      match_cont j (call_cont K_src) (call_cont K_tgt).
  Proof.
    revert K_tgt MATCH. induction K_src; ss; i; inv MATCH; ss; eauto.
    - econs.
    - econs; eauto.
  Qed.

  Lemma match_env_incr j0 j1
        (INCR: inject_incr j0 j1)
    :
      match_env j0 <2= match_env j1.
  Proof.
    ii. destruct (PR id).
    - des. left. esplits; eauto.
    - des. right. esplits; eauto.
  Qed.

  Lemma match_temp_env_incr j0 j1
        (INCR: inject_incr j0 j1)
    :
      match_temp_env j0 <2= match_temp_env j1.
  Proof.
    ii. destruct (PR id); econs. eapply val_inject_incr; eauto.
  Qed.

  Lemma match_cont_incr j0 j1
        (INCR: inject_incr j0 j1)
    :
      match_cont j0 <2= match_cont j1.
  Proof.
    ii. revert INCR.
    induction PR; i; econs; eauto; try by (eapply match_expr_incr; eauto).
    - eapply match_env_incr; eauto.
    - eapply match_temp_env_incr; eauto.
  Qed.

  Lemma bind_parameters_inject e_src e_tgt sm0 idl vargs_src vargs_tgt m_src1
        (BIND: bind_parameters ge_src e_src (SimMemInj.src sm0) idl vargs_src m_src1)
        (ENV: match_env (SimMemInj.inj sm0) e_src e_tgt)
        (MWF: SimMemInj.wf' sm0)
        (VALS: Val.inject_list (SimMemInj.inj sm0) vargs_src vargs_tgt)
    :
      exists sm1,
        (<<MEMSRC: SimMemInj.src sm1 = m_src1>>) /\
        (<<MWF: SimMemInj.wf' sm1>>) /\
        (<<MLE: SimMemInj.le' sm0 sm1>>) /\
        (<<BIND: bind_parameters ge_tgt e_tgt (SimMemInj.tgt sm0) idl vargs_tgt (SimMemInj.tgt sm1)>>).
  Proof.
    revert sm0 ENV vargs_src vargs_tgt m_src1 MWF VALS BIND. induction idl.
    - i. inv BIND. inv VALS. esplits; eauto.
      + refl.
      + econs.
    - i. inv BIND. inv VALS.
      destruct (ENV id); des; clarify.
      exploit assign_loc_inject; eauto. i. des. clarify.
      exploit IHidl; try apply H6; eauto.
      { inv MLE. eapply match_env_incr; eauto. }
      { inv MLE. eapply val_inject_list_incr; eauto. }
      i. des. esplits; eauto.
      + etrans; eauto.
      + econs; eauto. rewrite CENV in *. auto.
  Qed.

  Lemma set_match_temp_env j id v_src v_tgt tenv_src tenv_tgt
        (TENV: match_temp_env j tenv_src tenv_tgt)
        (VAL: Val.inject j v_src v_tgt)
    :
      match_temp_env j (PTree.set id v_src tenv_src) (PTree.set id v_tgt tenv_tgt).
  Proof.
    ii. repeat rewrite PTree.gsspec. des_ifs.
    econs; eauto.
  Qed.

  Lemma bind_parameter_temps_inject tenv_src0 tenv_tgt0 tenv_src1
        j idl vargs_src vargs_tgt
        (BIND: bind_parameter_temps idl vargs_src tenv_src0 = Some tenv_src1)
        (TENV: match_temp_env j tenv_src0 tenv_tgt0)
        (VALS: Val.inject_list j vargs_src vargs_tgt)
    :
      exists tenv_tgt1,
        (<<BIND: bind_parameter_temps idl vargs_tgt tenv_tgt0 = Some tenv_tgt1>>) /\
        (<<TENV: match_temp_env j tenv_src1 tenv_tgt1>>).
  Proof.
    revert tenv_src0 tenv_tgt0 tenv_src1 vargs_src BIND TENV vargs_tgt VALS.
    induction idl; i; ss; des_ifs_safe.
    - inv VALS. esplits; eauto.
    - inv VALS. exploit IHidl; eauto.
      eapply set_match_temp_env; eauto.
  Qed.

  Lemma create_undef_temps_match j l
    :
      match_temp_env j (create_undef_temps l) (create_undef_temps l).
  Proof.
    induction l; ss.
    - ii. repeat rewrite PTree.gempty. econs.
    - ii. des_ifs. rewrite PTree.gsspec.
      des_ifs. econs. eauto.
  Qed.

  Lemma function_entry1_inject
    :
      function_entry_inject function_entry1.
  Proof.
    ii. inv ENTRY.
    exploit alloc_variables_inject; eauto.
    { instantiate (1:=empty_env). ii. right.
      unfold empty_env. repeat rewrite PTree.gempty. auto. }
    i. des. clarify.
    exploit bind_parameters_inject; eauto.
    { cinv MLE. eapply val_inject_list_incr; eauto. } i. des.
    esplits; eauto.
    - cinv MLE. cinv MLE0. eapply match_env_incr; eauto.
    - eapply create_undef_temps_match.
    - etrans; eauto.
    - econs; eauto.
  Qed.

  Lemma function_entry2_inject
    :
      function_entry_inject function_entry2.
  Proof.
    ii. inv ENTRY.
    exploit alloc_variables_inject; eauto.
    { instantiate (1:=empty_env). ii. right.
      unfold empty_env. repeat rewrite PTree.gempty. auto. }
    i. des. clarify.
    exploit bind_parameter_temps_inject; eauto.
    { eapply create_undef_temps_match. } i. des.
    esplits; eauto.
    - cinv MLE. eapply match_temp_env_incr; eauto.
    - econs; eauto.
  Qed.

  Variable function_entry: genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
  Hypothesis FUNCTIONENTRY: function_entry_inject function_entry.

  Lemma deref_loc_inject j ty m_src m_tgt blk_src blk_tgt ofs_src ofs_tgt v_src
        (DEREF: deref_loc ty m_src blk_src ofs_src v_src)
        (INJECT: Mem.inject j m_src m_tgt)
        (VAL: Val.inject j (Vptr blk_src ofs_src) (Vptr blk_tgt ofs_tgt))
    :
      exists v_tgt,
        (<<DEREF: deref_loc ty m_tgt blk_tgt ofs_tgt v_tgt>>) /\
        (<<VAL: Val.inject j v_src v_tgt>>).
  Proof.
    inv DEREF.
    - exploit Mem.loadv_inject; eauto. i. des.
      esplits; eauto. econs 1; eauto.
    - esplits; eauto. econs 2; eauto.
    - esplits; eauto. econs 3; eauto.
  Qed.

  Lemma eval_expr_lvalue_inject j env_src env_tgt tenv_src tenv_tgt m_src m_tgt
        (GENV: meminj_match_globals eq ge_src ge_tgt j)
    :
      (forall
          exp v_src
          (EVAL: eval_expr ge_src env_src tenv_src m_src exp v_src),
          forall
            (ENV: match_env j env_src env_tgt)
            (TENV: match_temp_env j tenv_src tenv_tgt)
            (INJECT: Mem.inject j m_src m_tgt),
          exists v_tgt,
            (<<EVAL: eval_expr ge_tgt env_tgt tenv_tgt m_tgt exp v_tgt>>) /\
            (<<INJ: Val.inject j v_src v_tgt>>)) /\
      (forall
          exp blk_src ofs_src
          (EVAL: eval_lvalue ge_src env_src tenv_src m_src exp blk_src ofs_src),
          forall
            (ENV: match_env j env_src env_tgt)
            (TENV: match_temp_env j tenv_src tenv_tgt)
            (INJECT: Mem.inject j m_src m_tgt),
          exists blk_tgt ofs_tgt,
            (<<EVAL: eval_lvalue ge_tgt env_tgt tenv_tgt m_tgt exp blk_tgt ofs_tgt>>) /\
            (<<INJ: Val.inject j (Vptr blk_src ofs_src) (Vptr blk_tgt ofs_tgt)>>)).
  Proof.
    apply eval_expr_lvalue_ind; i.
    - esplits; eauto. econs 1; eauto.
    - esplits; eauto. econs 2; eauto.
    - esplits; eauto. econs 3; eauto.
    - esplits; eauto. econs 4; eauto.
    - cinv (TENV id); rewrite H in *; clarify.
      esplits; eauto. econs 5; eauto.
    - exploit H0; eauto. i. des.
      esplits; eauto. econs 6; eauto.
    - exploit H0; eauto. i. des.
      exploit sem_unary_operation_inject; eauto. i. des.
      esplits; eauto. econs 7; eauto.
    - exploit H0; eauto. i. des.
      exploit H2; eauto. i. des.
      exploit sem_binary_operation_inject; eauto. i. des.
      esplits; eauto. econs 8; eauto.
      rewrite <- CENV. auto.
    - exploit H0; eauto. i. des.
      exploit sem_cast_inject; eauto. i. des.
      esplits; eauto. econs 9; eauto.
    - esplits; eauto. rewrite CENV. econs 10; eauto.
    - esplits; eauto. rewrite CENV. econs 11; eauto.
    - exploit H0; eauto. i. des.
      exploit deref_loc_inject; eauto. i. des.
      esplits; eauto. econs 12; eauto.
    - cinv (ENV id); des; rewrite H in *; clarify.
      esplits; eauto. econs 1; eauto.
    - cinv (ENV id); des; rewrite H in *; clarify.
      inv GENV. exploit SYMBLE; eauto. i. des.
      esplits; eauto. econs 2; eauto.
    - exploit H0; eauto. i. des. cinv INJ.
      esplits; eauto. econs 3; eauto.
    - exploit H0; eauto. i. des. cinv INJ. rewrite CENV in *.
      esplits.
      + econs 4; eauto.
      + econs; eauto.
        repeat rewrite Ptrofs.add_assoc. f_equal.
        apply Ptrofs.add_commut.
    - exploit H0; eauto. i. des. cinv INJ. rewrite CENV in *.
      esplits; eauto. econs 5; eauto.
  Qed.

  Lemma eval_expr_inject j env_src env_tgt tenv_src tenv_tgt m_src m_tgt
        exp v_src
        (EVAL: eval_expr ge_src env_src tenv_src m_src exp v_src)
        (GENV: meminj_match_globals eq ge_src ge_tgt j)
        (ENV: match_env j env_src env_tgt)
        (TENV: match_temp_env j tenv_src tenv_tgt)
        (INJECT: Mem.inject j m_src m_tgt)
    :
      exists v_tgt,
        (<<EVAL: eval_expr ge_tgt env_tgt tenv_tgt m_tgt exp v_tgt>>) /\
        (<<INJ: Val.inject j v_src v_tgt>>).
  Proof.
    exploit eval_expr_lvalue_inject; eauto. i. des. eauto.
  Qed.

  Lemma eval_exprlist_inject j env_src env_tgt tenv_src tenv_tgt m_src m_tgt tys
        exps vs_src
        (EVALS: eval_exprlist ge_src env_src tenv_src m_src exps tys vs_src)
        (GENV: meminj_match_globals eq ge_src ge_tgt j)
        (ENV: match_env j env_src env_tgt)
        (TENV: match_temp_env j tenv_src tenv_tgt)
        (INJECT: Mem.inject j m_src m_tgt)
    :
      exists vs_tgt,
        (<<EVALS: eval_exprlist ge_tgt env_tgt tenv_tgt m_tgt exps tys vs_tgt>>) /\
        (<<INJ: Val.inject_list j vs_src vs_tgt>>).
  Proof.
    revert tys vs_src EVALS ENV TENV INJECT. induction exps; i.
    - inv EVALS. exists []. esplits; eauto. econs; eauto.
    - inv EVALS. exploit IHexps; eauto. i. des.
      exploit eval_expr_inject; eauto. i. des.
      exploit sem_cast_inject; eauto. i. des.
      exists (tv :: vs_tgt). esplits; eauto.
      econs; eauto.
  Qed.

  Lemma eval_lvalue_inject j env_src env_tgt tenv_src tenv_tgt m_src m_tgt
        exp blk_src ofs_src
        (EVAL: eval_lvalue ge_src env_src tenv_src m_src exp blk_src ofs_src)
        (GENV: meminj_match_globals eq ge_src ge_tgt j)
        (ENV: match_env j env_src env_tgt)
        (TENV: match_temp_env j tenv_src tenv_tgt)
        (INJECT: Mem.inject j m_src m_tgt)
    :
      exists blk_tgt ofs_tgt,
        (<<EVAL: eval_lvalue ge_tgt env_tgt tenv_tgt m_tgt exp blk_tgt ofs_tgt>>) /\
        (<<INJ: Val.inject j (Vptr blk_src ofs_src) (Vptr blk_tgt ofs_tgt)>>).
  Proof.
    exploit eval_expr_lvalue_inject; eauto. i. des. eauto.
  Qed.

  Definition match_loc j (loc_src loc_tgt: block * Z * Z): Prop :=
    match loc_src with
    | (blk_src, lo_src, hi_src) =>
      match loc_tgt with
      | (blk_tgt, lo_tgt, hi_tgt) =>
        exists delta,
        (<<DELTA: j blk_src = Some (blk_tgt, delta)>>) /\
        (<<LO: lo_src + delta = lo_tgt>>) /\
        (<<HI: hi_src + delta = hi_tgt>>)
      end
    end.

  Lemma free_list_inject_parallel
        sm0 locs_src locs_tgt m_src1
        (MWF: SimMemInj.wf' sm0)
        (LOCS: list_forall2 (match_loc (SimMemInj.inj sm0)) locs_src locs_tgt)
        (FREE: Mem.free_list (SimMemInj.src sm0) locs_src = Some m_src1)
    :
      exists sm1,
        (<<MEMSRC: SimMemInj.src sm1 = m_src1>>) /\
        (<<MWF: SimMemInj.wf' sm1>>) /\
        (<<MLE: SimMemInj.le' sm0 sm1>>) /\
        (<<FREE: Mem.free_list (SimMemInj.tgt sm0) locs_tgt = Some (SimMemInj.tgt sm1)>>).
  Proof.
    revert sm0 locs_tgt m_src1 MWF LOCS FREE. induction locs_src; ss.
    - i. clarify. inv LOCS. esplits; eauto. refl.
    - i. inv LOCS. unfold match_loc in H1. des_ifs. des. clarify. ss.
      exploit SimMemInj.free_parallel; eauto. i. des. clarify.
      exploit IHlocs_src; eauto.
      { eapply list_forall2_imply; eauto. i. unfold match_loc in *. des_ifs.
        des. inv MLE. esplits; eauto. }
      i. des. clarify.
      esplits; eauto.
      + etrans; eauto.
      + ss. rewrite FREETGT. eauto.
  Qed.

  Lemma blocks_of_env_match j e_src e_tgt
        (ENV: match_env j e_src e_tgt)
    :
      list_forall2 (match_loc j) (blocks_of_env ge_src e_src) (blocks_of_env ge_tgt e_tgt).
  Proof.
    set (R:=(fun (d_src d_tgt: block * type) =>
               let (b_src, t_src) := d_src in
               let (b_tgt, t_tgt) := d_tgt in
               (<<INJ: j b_src = Some (b_tgt, 0)>>) /\
               (<<TYSAME: t_src = t_tgt>>))).
    exploit PTree.elements_canonical_order.
    - instantiate (1:=R).
      instantiate (1:=e_tgt).
      instantiate (1:=e_src).
      i. destruct (ENV i); des; clarify.
      esplits; eauto. ss.
    - i. destruct (ENV i); des; clarify.
      esplits; eauto. ss.
    - intros ALL.
      unfold blocks_of_env. revert ALL.
      generalize (PTree.elements e_tgt).
      generalize (PTree.elements e_src).
      induction l; ss; i.
      + inv ALL. econs.
      + inv ALL. ss. econs; eauto.
        unfold block_of_binding. des_ifs; ss; des; clarify.
        esplits; eauto.
        rewrite CENV. zsimpl. auto.
  Qed.

  Scheme statement_ind2 := Induction for statement Sort Prop
    with labeled_statements_ind2 := Induction for labeled_statements Sort Prop.
  Combined Scheme statement_labeled_statements_ind from statement_ind2, labeled_statements_ind2.

  Lemma find_label_label_ls_match_none j lbl
    :
      (forall stmt,
          forall K_src0 K_tgt0
                 (LABEL: find_label lbl stmt K_src0 = None)
                 (CONT: match_cont j K_src0 K_tgt0),
            find_label lbl stmt K_tgt0 = None) /\
      (forall ls,
          forall K_src0 K_tgt0
                 (LABEL: find_label_ls lbl ls K_src0 = None)
                 (CONT: match_cont j K_src0 K_tgt0),
            find_label_ls lbl ls K_tgt0 = None).
  Proof.
    eapply statement_labeled_statements_ind; ss; i.
    - des_ifs_safe. exploit H; eauto.
      { econs; eauto. } intros LABEL0.
      rewrite LABEL0. eauto.
    - des_ifs_safe. exploit H; eauto. intros LABEL0.
      exploit H0; eauto. intros LABEL1.
      rewrite LABEL0. eauto.
    - des_ifs_safe. exploit H; eauto.
      { econs; eauto. } intros LABEL0.
      exploit H0; eauto.
      { econs; eauto. } intros LABEL1.
      rewrite LABEL0. eauto.
    - exploit H; eauto. econs; eauto.
    - des_ifs. exploit H; eauto.
    - des_ifs_safe. exploit H; eauto.
      { econs; eauto. } intros LABEL0.
      rewrite LABEL0.
      exploit H0; eauto.
  Qed.

  Lemma find_label_match_none j lbl stmt K_src0 K_tgt0
        (LABEL: find_label lbl stmt K_src0 = None)
        (CONT: match_cont j K_src0 K_tgt0)
    :
      find_label lbl stmt K_tgt0 = None.
  Proof.
    eapply find_label_label_ls_match_none; eauto.
  Qed.

  Lemma find_label_label_ls_match j lbl
    :
      (forall
          stmt K_src0 K_tgt0 stmt' K_src1
          (LABEL: find_label lbl stmt K_src0 = Some (stmt', K_src1))
          (CONT: match_cont j K_src0 K_tgt0),
          exists K_tgt1,
            (<<LABEL: find_label lbl stmt K_tgt0 = Some (stmt', K_tgt1)>>) /\
            (<<CONT: match_cont j K_src1 K_tgt1>>)) /\
      (forall
          ls K_src0 K_tgt0 stmt' K_src1
          (LABEL: find_label_ls lbl ls K_src0 = Some (stmt', K_src1))
          (CONT: match_cont j K_src0 K_tgt0),
          exists K_tgt1,
            (<<LABEL: find_label_ls lbl ls K_tgt0 = Some (stmt', K_tgt1)>>) /\
            (<<CONT: match_cont j K_src1 K_tgt1>>)).
  Proof.
    eapply statement_labeled_statements_ind; ss; i.
    - destruct (find_label lbl s (Kseq s0 K_src0)) eqn:LABEL0.
      + clarify. exploit H; eauto.
        { econs; eauto. } i. des.
        rewrite LABEL. esplits; eauto.
      + exploit H0; eauto. i. des.
        exploit find_label_match_none; eauto.
        { econs; eauto. } intros LABEL2.
        rewrite LABEL1. rewrite LABEL2. esplits; eauto.
    - destruct (find_label lbl s K_src0) eqn:LABEL0.
      + clarify. exploit H; eauto. i. des.
        rewrite LABEL. esplits; eauto.
      + exploit find_label_match_none; eauto.
        intros LABEL1. rewrite LABEL1.
        exploit H0; eauto.
    - destruct (find_label lbl s (Kloop1 s s0 K_src0)) eqn:LABEL0.
      + clarify. exploit H; eauto.
        { econs; eauto. } i. des.
        rewrite LABEL. esplits; eauto.
      + exploit find_label_match_none; eauto.
        { econs; eauto. }
        intros LABEL1. rewrite LABEL1.
        exploit H0; eauto.
        econs; eauto.
    - exploit H; eauto.
      econs; eauto.
    - des_ifs.
      + esplits; eauto.
      + exploit H; eauto.
    - destruct (find_label lbl s (Kseq (seq_of_labeled_statement l) K_src0)) eqn:LABEL0.
      + clarify. exploit H; eauto.
        { econs; eauto. } i. des.
        rewrite LABEL. esplits; eauto.
      + exploit find_label_match_none; eauto.
        { econs; eauto. }
        intros LABEL1. rewrite LABEL1.
        exploit H0; eauto.
  Qed.

  Lemma find_label_match j lbl stmt K_src0 K_tgt0 stmt' K_src1
        (LABEL: find_label lbl stmt K_src0 = Some (stmt', K_src1))
        (CONT: match_cont j K_src0 K_tgt0)
    :
      exists K_tgt1,
        (<<LABEL: find_label lbl stmt K_tgt0 = Some (stmt', K_tgt1)>>) /\
        (<<CONT: match_cont j K_src1 K_tgt1>>)
  .
  Proof.
    eapply find_label_label_ls_match; eauto.
  Qed.

  Lemma clight_step_preserve_injection
        sm_arg u st_src0 st_tgt0 st_src1 sm0 tr
        (SYMBOLS: symbols_inject (SimMemInj.inj sm0) se_src se_tgt)
        (GENV: meminj_match_globals eq ge_src ge_tgt (SimMemInj.inj sm0))
        (MATCH: match_states_clight sm_arg u st_src0 st_tgt0 sm0)
        (STEP: step se_src ge_src (function_entry ge_src) st_src0 tr st_src1)
    :
      exists st_tgt1 sm1,
        (<<STEP: step se_tgt ge_tgt (function_entry ge_tgt) st_tgt0 tr st_tgt1>>) /\
        (<<MATCH: match_states_clight sm_arg u st_src1 st_tgt1 sm1>>) /\
        (<<MLE: SimMemInj.le' sm0 sm1>>).
  Proof.
    inv STEP; inv MATCH; inv MATCHST.
    - cinv MWF. exploit eval_expr_inject; eauto. i. des.
      exploit eval_lvalue_inject; eauto. i. des.
      exploit sem_cast_inject; eauto. i. des.
      exploit assign_loc_inject; eauto. i. des.
      rewrite CENV in *.
      esplits.
      + econs 1; eauto.
      + cinv MLE. econs; eauto. econs; eauto.
        * eapply match_env_incr; eauto.
        * eapply match_temp_env_incr; eauto.
        * eapply match_cont_incr; eauto.
      + eauto.

    - cinv MWF. exploit eval_expr_inject; eauto. i. des. esplits.
      + econs 2; eauto.
      + econs; eauto. econs; eauto.
        eapply set_match_temp_env; eauto.
      + refl.

    - cinv MWF. exploit eval_exprlist_inject; eauto. i. des.
      exploit eval_expr_inject; eauto. i. des. esplits.
      + econs 3; eauto.
      + econs; eauto. econs; eauto. econs; eauto.
      + refl.

    - cinv MWF. exploit eval_exprlist_inject; eauto. i. des.
      exploit external_call_mem_inject_gen; eauto. i. des.
      exploit SimMemInjC.parallel_gen; eauto.
      { ii. eapply external_call_max_perm; eauto. }
      { ii. eapply external_call_max_perm; eauto. }
      i. des. esplits; eauto.
      + econs 4; eauto.
      + cinv MLE. econs; eauto. econs; eauto.
        * eapply match_env_incr; eauto.
        * unfold set_opttemp. des_ifs.
          { eapply set_match_temp_env; eauto.
            eapply match_temp_env_incr; eauto. }
          { eapply match_temp_env_incr; eauto. }
        * eapply match_cont_incr; eauto.

    - esplits.
      + econs 5; eauto.
      + econs; eauto. econs; eauto. econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 6; eauto.
      + econs; eauto. econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 7; eauto.
      + econs; eauto. econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 8; eauto.
      + econs; eauto. econs; eauto.
      + refl.

    - cinv MWF. exploit eval_expr_inject; eauto. i. des.
      exploit bool_val_inject; eauto. i. esplits.
      + econs 9; eauto.
      + econs; eauto. econs; eauto.
      + refl.

    - esplits.
      + econs 10; eauto.
      + econs; eauto. econs; eauto. econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 11; eauto.
      + econs; eauto. econs; eauto. econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 12; eauto.
      + econs; eauto. econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 13; eauto.
      + econs; eauto. econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 14; eauto.
      + econs; eauto. econs; eauto.
      + refl.

    - exploit free_list_inject_parallel; eauto.
      { eapply blocks_of_env_match; eauto. } i. des.
      esplits.
      + econs 15; eauto.
      + econs; eauto. clarify. econs; eauto. eapply call_cont_match; eauto.
        cinv MLE. eapply match_cont_incr; eauto.
      + eauto.

    - cinv MWF. exploit eval_expr_inject; eauto. i. des.
      exploit sem_cast_inject; eauto. i. des.
      exploit free_list_inject_parallel; eauto.
      { eapply blocks_of_env_match; eauto. } i. des.
      esplits.
      + econs 16; eauto.
      + econs; eauto. clarify. econs; eauto.
        * cinv MLE. eapply val_inject_incr; eauto.
        * eapply call_cont_match; eauto.
          cinv MLE. eapply match_cont_incr; eauto.
      + eauto.

    - cinv MWF. exploit free_list_inject_parallel; eauto.
      { eapply blocks_of_env_match; eauto. } i. des.
      esplits.
      + econs 17; eauto.
        unfold is_call_cont in *. destruct CONT; clarify.
      + econs; eauto. clarify. econs; eauto.
        cinv MLE. eapply match_cont_incr; eauto.
      + eauto.

    - cinv MWF. exploit eval_expr_inject; eauto. i. des.
      assert (SWITCH: sem_switch_arg v_tgt (typeof a) = Some n).
      { unfold sem_switch_arg in *. inv INJ; ss; clarify; des_ifs. }
      esplits.
      + econs 18; eauto.
      + econs; eauto. clarify. econs; eauto. econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 19; eauto.
      + econs; eauto. clarify. econs; eauto.
      + refl.

    - inv CONT. esplits.
      + econs 20; eauto.
      + econs; eauto. clarify. econs; eauto.
      + refl.

    - esplits.
      + econs 21; eauto.
      + econs; eauto. clarify. econs; eauto.
      + refl.

    - exploit find_label_match; eauto.
      { eapply call_cont_match; eauto. } i. des.
      esplits.
      + econs 22; eauto.
      + econs; eauto. clarify. econs; eauto.
      + refl.

    - exploit match_globals_find_funct; eauto. intros FPTRTGT.
      exploit FUNCTIONENTRY; eauto. i. des.
      esplits.
      + econs 23; eauto.
      + econs; eauto. clarify. econs; eauto.
        cinv MLE. eapply match_cont_incr; eauto.
      + eauto.

    - cinv MWF. exploit match_globals_find_funct; eauto. intros FPTRTGT.
      exploit external_call_mem_inject_gen; eauto. i. des.
      exploit SimMemInjC.parallel_gen; eauto.
      { ii. eapply external_call_max_perm; eauto. }
      { ii. eapply external_call_max_perm; eauto. }
      i. des. esplits; eauto.
      + econs 24; eauto.
      + cinv MLE. econs; eauto. econs; eauto.
        eapply match_cont_incr; eauto.

    - inv CONT. esplits.
      + econs 25; eauto.
      + econs; eauto. clarify. econs; eauto. destruct optid; ss.
        eapply set_match_temp_env; eauto.
      + refl.
  Qed.

  Lemma clight_step_preserve_injection2
        st_src0 st_tgt0 st_src1 j0 m_src0 m_tgt0 tr
        (SYMBOLS: symbols_inject j0 se_src se_tgt)
        (GENV: meminj_match_globals eq ge_src ge_tgt j0)
        (INJECT: Mem.inject j0 m_src0 m_tgt0)
        (MATCH: match_states_clight_internal st_src0 st_tgt0 j0 m_src0 m_tgt0)
        (STEP: step se_src ge_src (function_entry ge_src) st_src0 tr st_src1)
    :
      exists st_tgt1 m_src1 m_tgt1 j1 ,
        (<<STEP: step se_tgt ge_tgt (function_entry ge_tgt) st_tgt0 tr st_tgt1>>) /\
        (<<MATCH: match_states_clight_internal st_src1 st_tgt1 j1 m_src1 m_tgt1>>) /\
        (<<INJECT: Mem.inject j1 m_src1 m_tgt1>>) /\
        (<<INCR: inject_incr j0 j1>>) /\
        (<<SEP: inject_separated j0 j1 m_src0 m_tgt0>>) /\
        (<<UNCHSRC: Mem.unchanged_on
                      (loc_unmapped j0)
                      m_src0 m_src1>>) /\
        (<<UNCHTGT: Mem.unchanged_on
                      (loc_out_of_reach j0 m_src0)
                      m_tgt0 m_tgt1>>) /\
        (<<MAXSRC: forall
            b ofs
            (VALID: Mem.valid_block m_src0 b)
          ,
            <<MAX: Mem.perm m_src1 b ofs Max <1= Mem.perm m_src0 b ofs Max>> >>) /\
        (<<MAXTGT: forall
            b ofs
            (VALID: Mem.valid_block m_tgt0 b)
          ,
            <<MAX: Mem.perm m_tgt1 b ofs Max <1= Mem.perm m_tgt0 b ofs Max>> >>).
  Proof.
    set (sm:=SimMemInj.mk
               m_src0 m_tgt0 j0
               (loc_unmapped j0 /2\ SimMemInj.valid_blocks m_src0)
               (loc_out_of_reach j0 m_src0 /2\ SimMemInj.valid_blocks m_tgt0)
               (Mem.nextblock m_src0)
               (Mem.nextblock m_tgt0) 1%positive 1%positive).
    assert (SYMBINJ: symbols_inject (SimMemInj.inj sm) se_src se_tgt).
    { eauto. }
    exploit clight_step_preserve_injection; eauto; ss.
    - econs; eauto. econs; ss; eauto.
      + refl.
      + refl.
      + xomega.
      + xomega.
    - instantiate (1:=sm). i. des. destruct sm1.
      inv MATCH0. inv MLE. inv MWF. ss.
      esplits; eauto.
      + inv FROZEN. ii. exploit NEW_IMPLIES_OUTSIDE; eauto. i. des.
        unfold Mem.valid_block. clear - OUTSIDE_SRC OUTSIDE_TGT. xomega.
      + eapply Mem.unchanged_on_implies; eauto.
        ii. ss.
      + eapply Mem.unchanged_on_implies; eauto.
        ii. ss.
  Qed.

End CLIGHTINJ.