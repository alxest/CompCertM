Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC Memory GlobalenvsC Events Smallstep.
Require Import Op Registers ClightC Renumber.
Require Import sflib.

Require Import MutrecHeader IntegersC.
Require Import StaticMutrecB StaticMutrecBspec.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
(* Require SimMemInjC. *)
Require SoundTop.
Require SimMemInjInv SimMemInjInvC.
Require Mach.
Require Import AsmC AsmregsC Conventions1C MemoryC AsmExtra.

Set Implicit Arguments.


Definition memoized_inv: SimMemInjInv.memblk_invariant :=
  fun mem =>
    exists i,
      (<<VINDEX: mem Mint32 0 = Some (Vint i)>>) /\
      (<<VSUM: mem Mint32 (size_chunk Mint32) = Some (Vint (sum i))>>).

Local Instance SimMemMemoized: SimMem.class := SimMemInjInvC.SimMemInjInv memoized_inv.

Definition symbol_memoized: ident -> Prop := eq _memoized.

Lemma memoized_inv_store_le i v_ind v_sum blk ofs0 ofs1 m_tgt0 m_tgt1
      (sm0 sm1: SimMemInjInv.t')
      (MWF: SimMem.wf sm0)
      (INVAR: sm0.(SimMemInjInv.mem_inv) blk)
      (OFSI: ofs0 = 0)
      (OFSV: ofs1 = size_chunk Mint32)
      (INDEX: v_ind = Vint i)
      (SUM: v_sum = Vint (sum i))
      (STR0: Mem.store Mint32 sm0.(SimMemInjInv.tgt) blk ofs0 v_ind = Some m_tgt0)
      (STR1: Mem.store Mint32 m_tgt0 blk ofs1 v_sum = Some m_tgt1)
      (MREL: sm1 = SimMemInjInv.mk sm0.(SimMemInjInv.src) m_tgt1 sm0.(SimMemInjInv.inj) sm0.(SimMemInjInv.mem_inv))
  :
    (<<MLE: SimMem.le sm0 sm1>>) /\
    (<<MWF: SimMem.wf sm1>>).
Proof.
  inv MWF. split.
  - econs; ss; eauto.
    + refl.
    + erewrite <- Mem.nextblock_store; eauto.
      erewrite <- Mem.nextblock_store; eauto. refl.
    + ii. clarify.
    + ii. eapply Mem.perm_store_2; eauto. eapply Mem.perm_store_2; eauto.
  - econs; ss; eauto.
    + eapply MemoryC.private_unchanged_inject; eauto.
      * instantiate (1:=~2 loc_out_of_reach (SimMemInjInv.inj sm0) (SimMemInjInv.src sm0)).
        etrans.
        { eapply Mem.store_unchanged_on; eauto.
          ii. eapply H0.
          eapply INVRANGE; eauto. }
        { eapply Mem.store_unchanged_on; eauto.
          ii. eapply H0.
          eapply INVRANGE; eauto. }
      * auto.
    + ii. exploit SAT; eauto. i. inv H. des. des_ifs.
      * assert (Mem.valid_access m_tgt1 Mint32 blk0 0 Writable).
        { eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto. }
        assert (Mem.valid_access m_tgt1 Mint32 blk0 (size_chunk Mint32) Writable).
        { eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto. }
        destruct (peq blk blk0).
        { clarify. exists (i). des_ifs. split.
          - erewrite Mem.load_store_other; try apply STR1; eauto.
            + erewrite Mem.load_store_same; eauto. ss.
            + ss. right. left. refl.
          - erewrite Mem.load_store_same; eauto. ss. }
        { exists x. des_ifs. split.
          - erewrite Mem.load_store_other; try apply STR1; eauto.
            erewrite Mem.load_store_other; try apply STR0; eauto.
          - erewrite Mem.load_store_other; try apply STR1; eauto.
            erewrite Mem.load_store_other; try apply STR0; eauto. }
    + i. unfold Mem.valid_block in *.
      erewrite Mem.nextblock_store; try apply STR1; eauto.
      erewrite Mem.nextblock_store; try apply STR0; eauto.
Qed.

Section SIMMODSEM.

Variable skenv_link: SkEnv.t.
Variable sm_link: SimMem.t.
Let md_src: Mod.t := (StaticMutrecBspec.module).
Let md_tgt: Mod.t := (AsmC.module prog).
Hypothesis (INCL: SkEnv.includes skenv_link md_src.(Mod.sk)).
Hypothesis (WF: SkEnv.wf skenv_link).
(* Let ge := (SkEnv.project skenv_link md_src.(Mod.sk)). *)
(* Let tge := (SkEnv.revive (SkEnv.project skenv_link md_tgt.(Mod.sk)). *)

Let tge := (skenv_link.(SkEnv.project) prog.(Sk.of_program fn_sig)).(SkEnv.revive) prog.
Definition msp: ModSemPair.t :=
  ModSemPair.mk (md_src skenv_link) (md_tgt skenv_link) symbol_memoized sm_link.

Inductive well_saved (initstk stk: block)
  : regset -> regset -> mem -> Prop :=
| well_saved_intro
    (STKWF: initstk <> stk)
    (init_rs rs: regset) m
    (INITSIG: tge.(Genv.find_funct) (init_rs # PC) = Some (Internal func_g))
    (INITRSPVAL: init_rs RSP = Vptr initstk Ptrofs.zero)
    (RANOTFPTR: forall blk ofs (RAVAL: init_rs RA = Vptr blk ofs),
        ~ Plt blk (Genv.genv_next skenv_link))
    (RSPVAL: rs RSP = Vptr stk Ptrofs.zero)
    (STKPERM: Mem.range_perm m stk 0 32 Cur Freeable)
    (RASAVED: Mem.loadv Mptr m (Val.offset_ptr (rs RSP) (Ptrofs.repr 24)) = Some (init_rs RA))
    (RSPSAVED: Mem.loadv Mptr m (Val.offset_ptr (rs RSP) Ptrofs.zero) = Some (init_rs RSP))
    (REGSAVED: forall mr (CALLEESAVE: Conventions1.is_callee_save mr)
                      (INREG: mr <> Machregs.BX), init_rs mr.(to_preg) = rs mr.(to_preg))
    (REGSAVEDSTK: Mem.loadv Many64 m (Val.addl (rs RSP) (Vlong (Int64.repr 8))) = Some (init_rs RBX))
  :
    well_saved
      initstk stk
      init_rs rs m.

Lemma well_saved_keep init_rs initstk stk rs0 rs1 m0 m1
      (SAVED: well_saved
                initstk stk
                init_rs rs0 m0)
      (REGSAME: forall mr (CALLEESAVE: Conventions1.is_callee_save mr)
                       (INREG: mr <> Machregs.BX),
          rs0 mr.(to_preg) = rs1 mr.(to_preg))
      (RSPSAME: rs0 RSP = rs1 RSP)
      (UNCHSTK: Mem.unchanged_on
                   (fun blk _ => blk = stk) m0 m1)
  :
    well_saved
      initstk stk
      init_rs rs1 m1.
Proof.
  inv SAVED. rewrite RSPVAL in *. ss. econs; eauto.
  - ii. eapply Mem.perm_unchanged_on; [apply UNCHSTK|..]; ss; eauto.
  - rewrite <- RSPSAME. ss. erewrite Mem.load_unchanged_on; eauto. ss.
  - rewrite <- RSPSAME. ss. erewrite Mem.load_unchanged_on; eauto. ss.
  - ii. erewrite REGSAVED; eauto.
  - ii. rewrite <- RSPSAME. ss. des_ifs. ss.
    erewrite Mem.load_unchanged_on; eauto. ss.
Qed.

Inductive curr_pc (v: val) (ofs: ptrofs): Prop :=
| curr_pc_intro
    blk
    (RSPC: v = Vptr blk ofs)
    (FINDF: Genv.find_funct_ptr tge blk = Some (Internal func_g))
.

Require Import mktac.
Require Import StoreArguments.


(* TODO: from LB *)
Lemma Mem_unchanged_on_strengthen P m0 m1
  :
    Mem.unchanged_on P m0 m1 <-> Mem.unchanged_on (SimMemInj.valid_blocks m0 /2\ P) m0 m1.
Proof.
  split; i.
  - eapply Mem.unchanged_on_implies; eauto. i. des. auto.
  - eapply Mem.unchanged_on_implies; eauto. ss.
Qed.

Inductive match_states (sm_init: SimMem.t)
  :
    nat -> StaticMutrecBspec.state -> AsmC.state -> SimMem.t -> Prop :=
| match_states_initial
    idx m_src sm0
    i stk initstk init_rs rs m_tgt
    (MCOMPATSRC: m_src = sm0.(SimMem.src))
    (MCOMPATTGT: m_tgt = sm0.(SimMem.tgt))
    (MWF: SimMem.wf sm0)
    (MLE: SimMem.le sm_init sm0)
    (SAVED: well_saved initstk stk init_rs rs m_tgt)
    (OUTSIDE: forall
        blk_src blk_tgt delta
        (DETLA: SimMemInjInv.inj sm0 blk_src = Some (blk_tgt, delta)),
        blk_tgt <> stk)
    (CURRPC: curr_pc (rs PC) (Ptrofs.repr 2))
    (ARG: rs RDI = Vint i)
    (RANGE: 0 <= i.(Int.intval) < MAX)
  :
    match_states sm_init idx (Callstate i m_src)
                 (AsmC.mkstate init_rs (Asm.State rs m_tgt)) sm0

| match_states_at_external
    idx m_src sm0
    i stk initstk init_rs rs m_tgt
    (MCOMPATSRC: m_src = sm0.(SimMem.src))
    (MCOMPATTGT: m_tgt = sm0.(SimMem.tgt))
    (MWF: SimMem.wf sm0)
    (MLE: SimMem.le sm_init sm0)
    (SAVED: well_saved initstk stk init_rs rs m_tgt)
    (OUTSIDE: forall
        blk_src blk_tgt delta
        (DETLA: SimMemInjInv.inj sm0 blk_src = Some (blk_tgt, delta)),
        blk_tgt <> stk)
    (CURRPC: curr_pc (rs PC) (Ptrofs.repr 12))
    (ARG: rs RBX = Vint i)
    (FARG: rs RDI = Vint (Int.sub i (Int.repr 1)))
  :
    match_states sm_init idx (Interstate i m_src)
                 (AsmC.mkstate init_rs (Asm.State rs m_tgt)) sm0

| match_states_after_external
    idx m_src sm0
    i stk initstk init_rs rs m_tgt
    (MCOMPATSRC: m_src = sm0.(SimMem.src))
    (MCOMPATTGT: m_tgt = sm0.(SimMem.tgt))
    (MWF: SimMem.wf sm0)
    (MLE: SimMem.le sm_init sm0)
    (SAVED: well_saved initstk stk init_rs rs m_tgt)
    (OUTSIDE: forall
        blk_src blk_tgt delta
        (DETLA: SimMemInjInv.inj sm0 blk_src = Some (blk_tgt, delta)),
        blk_tgt <> stk)
    (CURRPC: curr_pc (rs PC) (Ptrofs.repr 13))
    (ARG: rs RBX = Vint i)
    (SUM: rs RAX = Vint (sum (Int.sub i Int.one)))
  :
    match_states sm_init idx (Returnstate (sum i) m_src)
                 (AsmC.mkstate init_rs (Asm.State rs m_tgt))sm0

| match_states_final
    idx m_src sm0
    i stk initstk init_rs rs m_tgt
    (MCOMPATSRC: m_src = sm0.(SimMem.src))
    (MCOMPATTGT: m_tgt = sm0.(SimMem.tgt))
    (MWF: SimMem.wf sm0)
    (MLE: SimMem.le sm_init sm0)
    (SAVED: well_saved initstk stk init_rs rs m_tgt)
    (OUTSIDE: forall
        blk_src blk_tgt delta
        (DETLA: SimMemInjInv.inj sm0 blk_src = Some (blk_tgt, delta)),
        blk_tgt <> stk)
    (CURRPC: curr_pc (rs PC) (Ptrofs.repr 20))
    (ARG: rs RAX = Vint i)
  :
    match_states sm_init idx (Returnstate i m_src)
                 (AsmC.mkstate init_rs (Asm.State rs m_tgt)) sm0
.

(* TODO: from DempProof *)
Lemma E0_double:
  E0 = E0 ** E0.
Proof. auto. Qed.
Hint Resolve E0_double.

Lemma match_states_lxsim
      sm_init idx st_src0 st_tgt0 sm0
      (SIMSK: SimSymb.sim_skenv
                sm0 symbol_memoized
                (SkEnv.project skenv_link (Sk.of_program fn_sig prog))
                (SkEnv.project skenv_link (Sk.of_program fn_sig prog)))
      (MATCH: match_states sm_init idx st_src0 st_tgt0 sm0)
  :
    <<XSIM: lxsim (md_src skenv_link) (md_tgt skenv_link)
                  (fun st => unit -> exists su m_init, SoundTop.sound_state su m_init st)
                  sm_init (Ord.lift_idx lt_wf idx) st_src0 st_tgt0 sm0>>
.
Proof.
  destruct (Genv.find_symbol
              ((skenv_link.(SkEnv.project) prog.(Sk.of_program fn_sig)).(SkEnv.revive) prog)
              _memoized) as [b_memo|] eqn:BLK; cycle 1.
  { exfalso. clear - INCL BLK. inv INCL.
    exploit DEFS; eauto.
    - instantiate (2:=_memoized). ss.
    - i. des. admit "genv". }

  revert_until tge.
  pcofix CIH.
  i. pfold. inv MATCH.



  (* initial *)
  - intros _. inv CURRPC.

    assert (CMP: compare_ints
                   (Val.and (rs RDI) (rs RDI)) Vzero
                   (rs # RBX <- (rs RDI)) # PC <- (Vptr blk (Ptrofs.add (Ptrofs.repr 2) Ptrofs.one))
                   (SimMemInjInv.tgt sm0) ZF = if (Int.eq_dec i Int.zero) then Vtrue else Vfalse).
    { unfold compare_ints, nextinstr, Val.cmpu.
      repeat (rewrite Pregmap.gso; [| clarify; fail]).
      repeat rewrite Pregmap.gss.
      rewrite ARG. ss. rewrite Int.and_idem.
      exploit Int.eq_spec; eauto. i. des_ifs. }
    destruct (classic (i = Int.zero)).

    (* i = Int.zero *)
    + clarify. econs 1. i. econs.
      * admit "ez".
      * i. ss. inv STEPSRC; ss.

        esplits.
        {
          left. econs; eauto.
          { instantiate (1:=AsmC.mkstate _ _). split.
            - eapply modsem_determinate; eauto.
            - ss. econs; ss. econs; eauto.
              + des_ifs.
              + ss. }

          econs 2; eauto.
          { instantiate (1:=AsmC.mkstate _ _). split.
            - eapply modsem_determinate; eauto.
            - ss. econs; ss. econs; eauto.
              + unfold nextinstr.
                rewrite Pregmap.gss.
                rewrite Pregmap.gso; clarify.
                rewrite RSPC. ss.
              + des_ifs.
              + ss. }

          econs 2; eauto.
          { instantiate (1:=AsmC.mkstate _ _). split.
            - eapply modsem_determinate; eauto.
            - ss. econs; ss. econs; eauto.
              + unfold nextinstr.
                repeat rewrite Pregmap.gss.
                repeat (rewrite Pregmap.gso; [| clarify; fail]).
                repeat rewrite Pregmap.gss.
                repeat (rewrite Pregmap.gso; [| clarify; fail]).
                rewrite RSPC. ss.
              + des_ifs.
              + ss.
                unfold nextinstr.
                repeat rewrite Pregmap.gss.
                repeat (rewrite Pregmap.gso; [| clarify; fail]).
                repeat rewrite Pregmap.gss.
                repeat (rewrite Pregmap.gso; [| clarify; fail]).
                rewrite RSPC. ss. rewrite CMP. ss. }

          econs 2; eauto.
          { instantiate (1:=AsmC.mkstate _ _). split.
            - eapply modsem_determinate; eauto.
            - ss. econs; ss. econs; eauto.
              + unfold nextinstr.
                rewrite Pregmap.gss. ss.
              + des_ifs.
              + ss. }

          econs 2; eauto.
          { instantiate (1:=AsmC.mkstate _ _). split.
            - eapply modsem_determinate; eauto.
            - ss. econs; ss. econs; eauto.
              + unfold nextinstr_nf, undef_regs, nextinstr. ss.
              + des_ifs.
              + ss. }

          econs 1.
        }

        { refl. }

        { right. eapply CIH; eauto. econs 4; eauto.

          - eapply well_saved_keep; eauto.
            + admit "ez".
            + refl.

          - ss.
            unfold nextinstr_nf, nextinstr, undef_regs.
            repeat rewrite Pregmap.gss. econs; eauto.

          - ss.
            unfold nextinstr_nf, nextinstr, undef_regs.
            repeat (rewrite Pregmap.gso; [| clarify; fail]).
            repeat rewrite Pregmap.gss.
            admit "arithemetic". }

      * admit "spec receptive".

    (* i <> Int.zero *)
    +

      cinv MWF. ss.
      assert (INVAR: SimMemInjInv.mem_inv sm0 b_memo).
      { inv SIMSK. ss. inv INJECT.
        eapply INVCOMPAT; eauto. ss. }
      hexploit SAT; eauto. intros SAT0.
      specialize (SAT0 _ INVAR). destruct SAT0. des. des_ifs_safe.

      assert (CMP0:
                nextinstr
                  (compare_ints
                     (nextinstr_nf
                        (((compare_ints (Val.and (rs RDI) (rs RDI)) Vzero
                                        (rs # RBX <- (rs RDI)) # PC <-
                                        (Vptr blk (Ptrofs.add (Ptrofs.repr 2) Ptrofs.one))
                                        (SimMemInjInv.tgt sm0)) # PC <-
                                                                (Vptr blk (Ptrofs.add (Ptrofs.add (Ptrofs.repr 2) Ptrofs.one) Ptrofs.one)))
                           # PC <- (Vptr blk (Ptrofs.repr 8))) # RAX <- (Vint x) RBX)
                     (nextinstr_nf
                        (((compare_ints (Val.and (rs RDI) (rs RDI)) Vzero
                                        (rs # RBX <- (rs RDI)) # PC <-
                                        (Vptr blk (Ptrofs.add (Ptrofs.repr 2) Ptrofs.one))
                                        (SimMemInjInv.tgt sm0)) # PC <-
                                                                (Vptr blk (Ptrofs.add (Ptrofs.add (Ptrofs.repr 2) Ptrofs.one) Ptrofs.one)))
                           # PC <- (Vptr blk (Ptrofs.repr 8))) # RAX <- (Vint x) RAX)
                     (nextinstr_nf
                        (((compare_ints (Val.and (rs RDI) (rs RDI)) Vzero
                                        (rs # RBX <- (rs RDI)) # PC <-
                                        (Vptr blk (Ptrofs.add (Ptrofs.repr 2) Ptrofs.one))
                                        (SimMemInjInv.tgt sm0)) # PC <-
                                                                (Vptr blk (Ptrofs.add (Ptrofs.add (Ptrofs.repr 2) Ptrofs.one) Ptrofs.one)))
                           # PC <- (Vptr blk (Ptrofs.repr 8))) # RAX <- (Vint x))
                     (SimMemInjInv.tgt sm0)) ZF =
                if (Int.eq_dec x i) then Vtrue else Vfalse).
      { unfold compare_ints at 1.
        unfold nextinstr_nf, undef_regs, nextinstr.
        repeat (rewrite Pregmap.gso; [| clarify; fail]).
        repeat rewrite Pregmap.gss. ss.
        repeat (rewrite Pregmap.gso; [| clarify; fail]).
        repeat rewrite Pregmap.gss. ss.
        unfold Val.cmpu, Val.of_optbool, Val.cmpu_bool. ss.
        unfold compare_ints.
        repeat (rewrite Pregmap.gso; [| clarify; fail]).
        repeat rewrite Pregmap.gss.
        rewrite ARG.
        exploit Int.eq_spec; eauto. i. des_ifs. }

      destruct (Int.eq_dec x i).

      (* already memoized *)
      { clarify. econs 2. i. splits.
        - econs 2.
          + split.
            * apply star_one. ss. econs 1.
            * admit "index".
          + refl.
          + left. pfold. intros _. econs 1. i. econs 2.

            * esplits.
              {
                econs; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + des_ifs.
                    + ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      rewrite Pregmap.gss.
                      rewrite Pregmap.gso; clarify.
                      rewrite RSPC. ss.
                    + des_ifs.
                    + ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      repeat rewrite Pregmap.gss.
                      repeat (rewrite Pregmap.gso; [| clarify; fail]).
                      repeat rewrite Pregmap.gss.
                      repeat (rewrite Pregmap.gso; [| clarify; fail]).
                      rewrite RSPC. ss.
                    + des_ifs.
                    + ss.
                      unfold nextinstr.
                      repeat rewrite Pregmap.gss.
                      repeat (rewrite Pregmap.gso; [| clarify; fail]).
                      repeat rewrite Pregmap.gss.
                      repeat (rewrite Pregmap.gso; [| clarify; fail]).
                      rewrite RSPC. ss. rewrite CMP.
                      simpl.
                      des_ifs. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. unfold exec_load, eval_addrmode. ss.
                      unfold Genv.symbol_address. ss. rewrite BLK. psimpl.
                      des_ifs_safe. ss. psimpl.
                      replace (Ptrofs.unsigned (Ptrofs.of_int64 Int64.zero)) with 0; cycle 1.
                      { admit "arithmetic". }
                      rewrite VINDEX. ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr_nf, undef_regs, nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr_nf, undef_regs, nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. rewrite CMP0. ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. unfold exec_load, eval_addrmode. ss.
                      unfold Genv.symbol_address. ss. rewrite BLK. psimpl.
                      des_ifs_safe. ss.
                      replace (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr 4) (Ptrofs.of_int64 Int64.zero))) with 4; cycle 1.
                      { admit "arithmetic". }
                      rewrite VSUM. ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. }

                econs 1.
              }

              { admit "index". }

            * refl.

            * right. eapply CIH; eauto.
              econs 4; eauto.
              { eapply well_saved_keep; eauto.
                - admit "ez".
                - refl. }
              { unfold nextinstr_nf, nextinstr.
                repeat rewrite Pregmap.gss. ss. econs; eauto. }

        - admit "safe". }

      (* not memoized *)
      { clarify. econs 2. i. splits.
        - econs 2.
          + split.
            * apply star_one. ss. econs 2.
              admit "arithmetic".
            * admit "index".
          + refl.
          + left. pfold. intros _. econs 1. i. econs 2.

            * esplits.
              {
                econs; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + des_ifs.
                    + ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      rewrite Pregmap.gss.
                      rewrite Pregmap.gso; clarify.
                      rewrite RSPC. ss.
                    + des_ifs.
                    + ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      repeat rewrite Pregmap.gss.
                      repeat (rewrite Pregmap.gso; [| clarify; fail]).
                      repeat rewrite Pregmap.gss.
                      repeat (rewrite Pregmap.gso; [| clarify; fail]).
                      rewrite RSPC. ss.
                    + des_ifs.
                    + ss.
                      unfold nextinstr.
                      repeat rewrite Pregmap.gss.
                      repeat (rewrite Pregmap.gso; [| clarify; fail]).
                      repeat rewrite Pregmap.gss.
                      repeat (rewrite Pregmap.gso; [| clarify; fail]).
                      rewrite RSPC. ss. rewrite CMP.
                      simpl.
                      des_ifs. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. unfold exec_load, eval_addrmode. ss.
                      unfold Genv.symbol_address. ss. rewrite BLK. psimpl.
                      des_ifs_safe. ss. psimpl.
                      replace (Ptrofs.unsigned (Ptrofs.of_int64 Int64.zero)) with 0; cycle 1.
                      { admit "arithmetic". }
                      rewrite VINDEX. ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr_nf, undef_regs, nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr_nf, undef_regs, nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. rewrite CMP0. ss. }

                econs 2; eauto.
                { instantiate (1:=AsmC.mkstate _ _). split.
                  - eapply modsem_determinate; eauto.
                  - ss. econs; ss. econs; eauto.
                    + unfold nextinstr.
                      repeat rewrite Pregmap.gss. ss.
                    + des_ifs.
                    + ss. }

                econs 1.
              }

              { admit "index". }

            * refl.

            * right. eapply CIH; eauto.
              econs 2; eauto.
              { eapply well_saved_keep; eauto.
                - admit "ez".
                - refl. }
              { unfold nextinstr_nf, nextinstr.
                repeat rewrite Pregmap.gss. ss. econs; eauto. }
              { unfold nextinstr_nf, nextinstr.
                repeat rewrite Pregmap.gss.
                repeat (rewrite Pregmap.gso; [| clarify; fail]). ss.
                repeat rewrite Pregmap.gss.
                repeat (rewrite Pregmap.gso; [| clarify; fail]). ss.
                repeat rewrite Pregmap.gss.
                unfold compare_ints.
                repeat (rewrite Pregmap.gso; [| clarify; fail]). ss.
                repeat rewrite Pregmap.gss.
                rewrite ARG. ss. f_equal.
                admit "arithmetic". }

        - admit "safe".
      }

  - intros _. inv CURRPC.
    econs 1. i. econs 2.
    { split.
      - instantiate (1:=AsmC.mkstate _ _). apply plus_one. split.
        + eapply modsem_determinate; eauto.
        + ss. econs; ss. econs; eauto.
          * des_ifs.
          * ss.
      - admit "index". }
    { refl. }

    left. pfold. intros _. econs 3; eauto.
    + econs; eauto. econs; eauto.
      instantiate (1:=g_id). admit "genv".
    + ii.

      hexploit Mem.range_perm_free.
      { instantiate (1:=0).
        instantiate (1:=0).
        instantiate (1:=stk).
        instantiate (1:=SimMem.tgt sm0).
        ii. lia. } intros [m_tgt FREE].


      cinv MWF.
      hexploit (@SimMemInjInv.unchanged_on_mle
                  memoized_inv sm0
                  sm0.(SimMemInjInv.src) m_tgt sm0.(SimMemInjInv.inj)); ss; eauto.
      { eapply private_unchanged_inject; eauto.
        - eapply Mem.free_unchanged_on; eauto. ii. omega.
        - instantiate (1:=~2 loc_out_of_reach (SimMemInjInv.inj sm0) (SimMemInjInv.src sm0)).
          ss. }
      { ii. clarify. }
      { refl. }
      { eapply Mem.free_unchanged_on; eauto. ii. omega. }
      { ii. eapply Mem.perm_free_3; eauto. }
      i. des.

      cinv SAVED. inv ATSRC.
      eexists (Args.mk _ [Vint (Int.sub i (Int.repr 1))] _).
      esplits; eauto.
      * econs; ss; eauto.
        admit "genv".
      * econs; eauto.
        { repeat rewrite Pregmap.gss. ss.
          instantiate (1:=g_fptr).
          admit "genv". }
        { admit "genv". }
        { instantiate (1:=(mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default)).
          admit "genv". }
        { unfold size_arguments. des_ifs. }
        { econs; eauto.
          - econs; eauto. ss.
            rpapply extcall_arg_reg. ss.
          - econs. }
        { split; ss.
          - repeat (rewrite Pregmap.gso; [| clarify; fail]).
            rewrite Pregmap.gss. rewrite RSPC. ss.
          - repeat (rewrite Pregmap.gso; [| clarify; fail]).
            rewrite Pregmap.gss. rewrite RSPC. ss. }
        { ii. apply Z.divide_0_r. }
        { eauto. }

      * i. inv SIMRETV. inv AFTERSRC. ss.
        exploit Mem_unfree_suceeds.
        { instantiate (1:=stk).
          instantiate (1:=SimMemInjInv.tgt sm_ret).
          admit "ez". } i. des.
        eexists.
        eexists (SimMemInjInv.mk
                   (SimMemInjInv.src sm_ret)
                   m1
                   (SimMemInjInv.inj sm_ret)
                   (SimMemInjInv.mem_inv sm_ret)).
        eexists. esplits; ss; eauto.

        { econs; ss; eauto.
          - instantiate (1:=mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default).
            admit "genv".
          - unfold size_arguments. des_ifs. ss. psimpl.
            rewrite MEMTGT. eauto. }
        { admit "make lemma". }

        { right. eapply CIH; eauto.
          { admit "find lemma". }
          econs 3; ss; eauto.
          - admit "make lemma".
          - admit "make lemma".
          - eapply well_saved_keep; eauto.
            + admit "ez".
            + admit "ez".
          - admit "ez".
          - repeat rewrite Pregmap.gss. rewrite RSPC.
            repeat (rewrite Pregmap.gso; [| clarify; fail]).
            repeat rewrite Pregmap.gss. ss. econs; eauto.
          - unfold set_pair, loc_external_result, loc_result. des_ifs_safe. ss.
            clarify.
            repeat (rewrite Pregmap.gso; [| clarify; fail]).
            repeat rewrite Pregmap.gss.
            rewrite INT in *. inv RETV. auto. }

  - intros _. econs 1. i. cinv CURRPC.

    cinv MWF. ss.
    assert (INVAR: SimMemInjInv.mem_inv sm0 b_memo).
    { inv SIMSK. ss. inv INJECT.
      eapply INVCOMPAT; eauto. ss. }
    hexploit SAT; eauto. intros SAT0.
    specialize (SAT0 _ INVAR). destruct SAT0. des. des_ifs_safe.

    hexploit Mem.valid_access_store.
    { eapply v0. } intros [m_tgt0 STR0].
    hexploit Mem.valid_access_store.
    { eapply Mem.store_valid_access_1; eauto. } intros [m_tgt1 STR1].

    hexploit memoized_inv_store_le; try refl; eauto.
    instantiate (1:=i) in STR0. i. des.

    econs 2.

    + split.
      * econs 1; eauto.
        { instantiate (1:=AsmC.mkstate _ _). split.
          - eapply modsem_determinate; eauto.
          - ss. econs; ss. econs; eauto.
            + des_ifs.
            + ss. }

        econs 2; eauto.
        { instantiate (1:=AsmC.mkstate _ _). split.
          - eapply modsem_determinate; eauto.
          - ss. econs; ss. econs; eauto.
            + unfold nextinstr.
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              rewrite RSPC. ss.
            + des_ifs.
            + ss.
              unfold exec_store, Mem.storev, eval_addrmode. ss.
              des_ifs_safe. unfold Genv.symbol_address. rewrite BLK.
              psimpl. unfold nextinstr at 1.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              rewrite ARG.
              replace (Ptrofs.unsigned (Ptrofs.of_int64 Int64.zero)) with 0; cycle 1.
              { admit "arithmetic". }
              rewrite STR0.
              ss. }

        econs 2; eauto.
        { instantiate (1:=AsmC.mkstate _ _). split.
          - eapply modsem_determinate; eauto.
          - ss. econs; ss. econs; eauto.
            + unfold nextinstr_nf, undef_regs, nextinstr.
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              rewrite RSPC. ss.
            + des_ifs.
            + ss.
              unfold exec_store, Mem.storev, eval_addrmode. ss.
              des_ifs_safe. unfold Genv.symbol_address. rewrite BLK.
              psimpl. unfold nextinstr_nf at 1.
              unfold undef_regs. unfold nextinstr at 1 2.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              repeat rewrite Pregmap.gss. rewrite SUM.
              replace
                (Val.add (Vint (sum (Int.sub i Int.one))) (Vint (Int.add i (Int.repr 0))))
                with (Vint (sum i)); cycle 1.
              { admit "arithmetic". }
              rewrite STR1. ss. }

        econs 2; eauto.
        { instantiate (1:=AsmC.mkstate _ _). split.
          - eapply modsem_determinate; eauto.
          - ss. econs; ss. econs; eauto.
            + unfold nextinstr_nf, undef_regs, nextinstr.
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              rewrite RSPC. ss.
            + des_ifs.
            + ss. unfold goto_label.
              unfold nextinstr_nf, undef_regs, nextinstr.
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              repeat rewrite Pregmap.gss.
              repeat (rewrite Pregmap.gso; [| clarify; fail]).
              rewrite RSPC. ss. }

        econs 1; eauto.

      * admit "index".

    + eauto.

    + right. eapply CIH; eauto.
      { admit "ez". }
      econs 4; ss; eauto.

      * etrans; eauto.

      * eapply well_saved_keep; eauto.
        { admit "ez". }
        { admit "ez". }

      * repeat rewrite Pregmap.gss. econs; eauto.


  - admit "see well_saved final".

    Unshelve. all:admit"".
Qed.

(* Lemma well_saved_initial init_rs rs0 m0 arg *)
(*       (INITIAL: initial_frame *)
(*                   skenv_link prog arg *)
(*                   (AsmC.mkstate init_rs (Asm.State rs0 m0))) *)
(*   : *)
(*     exists fd initstk stk rs1 m1 rs2 m2, *)
(*       (<<ALLOCFRAME: exec_instr *)
(*                        tge fd (Pallocframe 32 (Ptrofs.repr 24) (Ptrofs.zero)) rs0 m0 = Next rs1 m1>>) /\ *)
(*       (<<PUSH: exec_instr *)
(*                  tge func_g *)
(*                  (Pmov_mr_a (Addrmode (Some RSP) None (inl 8)) RBX) *)
(*                  rs1 m1 = Next rs2 m2>>) /\ *)
(*       (<<SAVED: well_saved *)
(*                   initstk stk *)
(*                   (AsmC.mkstate init_rs (Asm.State rs2 m2))>>) *)
(* . *)
(* (* TODO: about fd and arguments, pc *) *)
(* (* TODO: about memory *) *)
(* Proof. *)
(*   inv INITIAL. cinv STORE. des. *)
(*   ss. destruct (Mem.alloc (JunkBlock.assign_junk_blocks m1 n) 0 32) as [m2 stk] eqn:ALLOC. *)
(*   hexploit Mem.valid_access_store. *)
(*   { eapply Mem.valid_access_implies. *)
(*     - instantiate (4:=Mptr). *)
(*       eapply Mem.valid_access_alloc_same. *)
(*       + eauto. *)
(*       + instantiate (1:=Ptrofs.unsigned Ptrofs.zero). ss. *)
(*       + unfold Mptr. des_ifs. *)
(*       + apply Z.divide_0_r. *)
(*     - econs. } intros [m3 STR0]. *)
(*   psimpl. rewrite STR0. *)
(*   hexploit Mem.valid_access_store. *)
(*   { eapply Mem.valid_access_implies. *)
(*     - instantiate (4:=Mptr). *)
(*       eapply Mem.store_valid_access_1; eauto. *)
(*       eapply Mem.valid_access_alloc_same. *)
(*       + eauto. *)
(*       + instantiate (1:=Ptrofs.unsigned (Ptrofs.repr 24)). ss. *)
(*       + unfold Mptr. des_ifs. *)
(*       + rewrite align_chunk_Mptr. des_ifs. exists 3. ss. *)
(*     - econs. } intros [m4 STR1]. rewrite STR1. *)
(*   unfold exec_store, eval_addrmode, eval_addrmode64. des_ifs_safe. ss. *)
(*   hexploit Mem.valid_access_store. *)
(*   { eapply Mem.valid_access_implies. *)
(*     - instantiate (4:=Many64). *)
(*       eapply Mem.store_valid_access_1; eauto. *)
(*       eapply Mem.store_valid_access_1; eauto. *)
(*       eapply Mem.valid_access_alloc_same. *)
(*       + eauto. *)
(*       + instantiate (1:=Ptrofs.unsigned (Ptrofs.repr 8)). ss. *)
(*       + unfold Mptr. des_ifs. *)
(*       + ss. exists 2. auto. *)
(*     - econs. } intros [m5 STR2]. *)
(*   esplits; eauto. ss. des_ifs_safe. ss. *)

(*   - unfold Ptrofs.of_int64. psimpl. rewrite Int64.add_zero_l. *)
(*     rewrite STR2. eauto. *)
(*   - econs; ss; eauto. *)

(*     + eapply Mem.alloc_result in ALLOC. clarify. ii. *)
(*       cinv H0. eapply Mem.nextblock_alloc in ALC. rewrite ALC in NB. *)
(*       clear - NB H. *)
(*       exploit JunkBlock.assign_junk_blocks_unchanged_on. *)
(*       instantiate (1:=n). instantiate (1:=m1). i. *)
(*       eapply Mem.unchanged_on_nextblock in H0. *)
(*       rewrite <- NB in *. rewrite <- H in *. clear - H0. xomega. *)

(*     + admit "genv". *)

(*     + ii. *)
(*       eapply Mem.perm_store_1; eauto. *)
(*       eapply Mem.perm_store_1; eauto. *)
(*       eapply Mem.perm_store_1; eauto. *)
(*       eapply Mem.perm_alloc_2; eauto. *)

(*     + psimpl. erewrite Mem.load_store_other; eauto; cycle 1. *)
(*       { rewrite size_chunk_Mptr. des_ifs. ss. right. lia. } *)
(*       erewrite Mem.load_store_same; eauto. *)
(*       f_equal. erewrite <- Val.load_result_same; eauto. ss. *)

(*     + psimpl. erewrite Mem.load_store_other; eauto; cycle 1. *)
(*       { rewrite size_chunk_Mptr. des_ifs. ss. right. lia. } *)
(*       erewrite Mem.load_store_other; eauto; cycle 1. *)
(*       { rewrite size_chunk_Mptr. des_ifs. ss. right. lia. } *)
(*       erewrite Mem.load_store_same; eauto. *)
(*       f_equal. rewrite H1. ss. *)

(*     + i. unfold nextinstr_nf, nextinstr, undef_regs, to_preg, preg_of, Pregmap.set. *)
(*       des_ifs. *)

(*     + des_ifs. unfold Ptrofs.of_int64. psimpl. *)
(*       unfold nextinstr in STR2. *)
(*       repeat (rewrite Pregmap.gso in STR2; clarify). *)
(*       erewrite Mem.load_store_same; eauto. ss. *)
(* Qed. *)

(* Lemma well_saved_final initstk stk init_rs rs0 m0 *)
(*       (SAVED: well_saved *)
(*                 initstk stk *)
(*                 (AsmC.mkstate init_rs (Asm.State rs0 m0))) *)
(*   : *)
(*     exists rs1 rs2 rs3 m2 m4, *)
(*       (<<POP: exec_instr *)
(*                 tge func_g (Pmov_rm_a RBX (Addrmode (Some RSP) None (inl 8))) *)
(*                 rs0 m0 = Next rs1 m0>>) /\ *)
(*       (<<FREEFRAME: exec_instr *)
(*                       tge func_g (Pfreeframe 32 (Ptrofs.repr 24) Ptrofs.zero) rs1 m0 = Next rs2 m2>>) /\ *)
(*       (<<RET: exec_instr *)
(*                 tge func_g Pret rs2 m2 = Next rs3 m2>>) /\ *)
(*       (<<FREE: Mem.free m2 initstk 0 0 = Some m4>>) /\ *)
(*       (<<FINAL: final_frame *)
(*                   skenv_link prog *)
(*                   (AsmC.mkstate init_rs (Asm.State rs3 m2)) *)
(*                   (Retv.mk (rs0 RAX) m4) >>). *)
(* Proof. *)
(*   inv SAVED. ss. *)
(*   unfold exec_load, eval_addrmode, eval_addrmode64. des_ifs_safe. ss. *)
(*   rewrite Int64.add_zero_l. rewrite REGSAVEDSTK. *)
(*   hexploit Mem.range_perm_free. *)
(*   { eapply STKPERM. } intros [m2 FREE1]. *)
(*   hexploit Mem.range_perm_free. *)
(*   { instantiate (1:=0). *)
(*     instantiate (1:=0). *)
(*     instantiate (1:=initstk). *)
(*     instantiate (1:=m2). *)
(*     ii. omega. } intros [m4 FREE2]. *)
(*   exists (nextinstr_nf rs0 # RBX <- (init_rs RBX)). eexists. eexists. *)
(*   exists m2. exists m4. *)
(*   replace ((nextinstr_nf rs0 # RBX <- (init_rs RBX) RSP)) with (rs0 RSP); cycle 1. *)
(*   { unfold nextinstr_nf, nextinstr, undef_regs. *)
(*     repeat (rewrite Pregmap.gso; clarify). } *)
(*   rewrite RASAVED. rewrite RSPSAVED. rewrite RSPVAL. psimpl. zsimpl. *)
(*   rewrite FREE1. rewrite FREE2. esplits; eauto. *)
(*   replace (rs0 RAX) with *)
(*       ((nextinstr *)
(*           ((nextinstr_nf rs0 # RBX <- (init_rs RBX)) # RSP <- (init_rs RSP)) # RA <- *)
(*           (init_rs RA)) # PC <- *)
(*                         (nextinstr *)
(*                            ((nextinstr_nf rs0 # RBX <- (init_rs RBX)) # RSP <- (init_rs RSP)) # RA <- *)
(*                            (init_rs RA) RA) (to_preg Machregs.AX)); cycle 1. *)
(*   { unfold nextinstr, Pregmap.set, to_mreg, to_preg, preg_of. des_ifs. } *)
(*   econs; eauto. *)
(*   - i. eapply Val.lessdef_same. destruct (Machregs.mreg_eq mr Machregs.BX). *)
(*     + clarify. *)
(*     + erewrite REGSAVED; eauto. *)
(*       unfold nextinstr_nf, nextinstr, undef_regs, to_preg, preg_of, Pregmap.set. des_ifs. *)
(*   - unfold nextinstr, Pregmap.set, to_mreg, to_preg, preg_of. des_ifs. *)
(*     unfold external_state, Genv.find_funct, Genv.find_funct_ptr. des_ifs. *)
(*     exfalso. eapply RANOTFPTR; eauto. eapply Genv.genv_defs_range in Heq2; eauto. *)
(*   - unfold Genv.find_funct, Genv.find_funct_ptr. des_ifs. *)
(*     exfalso. eapply RANOTFPTR; eauto. eapply Genv.genv_defs_range; eauto. *)
(* Qed. *)


Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  econs; eauto.
  { i. eapply SoundTop.sound_state_local_preservation. }
  { i. eapply Preservation.local_preservation_noguarantee_weak; eauto. eapply SoundTop.sound_state_local_preservation. }
  i. ss. esplits; eauto.

  - i. des. inv SAFESRC. instantiate (1:=unit).
    esplits; eauto.
    + refl.
    + econs; eauto.
    + instantiate (1:= (Ord.lift_idx lt_wf 15%nat)).
      inv INITTGT. inv TYP. ss.
      assert (FD: fd = func_g).
      { admit "genv". } clarify.

      admit "see well_saved_initial".

  - (* init progress *)
    i.
    des. inv SAFESRC.
    inv SIMARGS; ss.

    exploit asm_initial_frame_succeed; eauto.
    + instantiate (1:=func_g). ss.
      eapply inject_list_length in VALS. des. rewrite <- VALS.
      rewrite VS. ss.
    + ss.
    + admit "genv".
Qed.


End SIMMODSEM.


Theorem sim_mod
  :
    ModPair.sim (ModPair.mk (StaticMutrecBspec.module) (AsmC.module prog) symbol_memoized)
.
Proof.
  econs; ss.
  - econs; ss. i. inv SS. esplits; ss; eauto.
    + econs; ss.
      admit "fill definition".
    + ii. des; clarify.
    + ii. destruct H. eapply in_prog_defmap in PROG.
      ss. unfold update_snd in PROG. ss.
      des; clarify; inv DROP; ss.
      des; clarify.
  - ii. ss.
    inv SIMSKENVLINK. inv SIMSKENV.
    eapply sim_modsem; eauto.
Qed.
