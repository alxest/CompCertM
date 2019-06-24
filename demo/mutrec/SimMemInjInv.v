Require Import CoqlibC.
Require Import MemoryC.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import AST.

Require Import IntegersC LinkingC.
Require Import SimSymb Skeleton Mod ModSem.
Require Import SimMem.
Require SimSymbId.
Require Import Conventions1.
Require MachC.
Require Export SimMemInj.
Require Import SimMemInjC.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.



Section MEMINJINV.

  Definition memblk_invariant := (memory_chunk -> Z -> option val) -> Prop.
  (* Definition memory_invariant := block -> memblk_invariant -> Prop. *)

  Variable P : memblk_invariant.

  (* Record t' := mk *)
  (*   { minj:> SimMemInj.t'; *)
  (*     src_genv_nb : block; *)
  (*     tgt_genv_nb : block; *)
  (*     mem_inv: block -> Prop; *)
  (*     (* mem_inv: block -> (memory_chunk -> Z -> option val -> Prop); *) *)
  (*   }. *)

  Record t' :=
    mk
      { src : mem;
        tgt : mem;
        inj : meminj;
        mem_inv: block -> Prop;
        (* mem_inv: memory_invariant; *)
      }.

  (* Definition tgt_private_nge (sm: t') := *)
  (*   (loc_out_of_reach sm.(inj) sm.(src)) *)
  (*     /2\ (valid_blocks sm.(tgt)) /2\ (fun blk _ => Ple blk sm.(tgt_genv_nb)). *)

  (* Definition src_private_nge (sm: t') := *)
  (*   (loc_unmapped sm.(inj)) *)
  (*     /2\ (valid_blocks sm.(src)) /2\ (fun blk _ => Ple blk sm.(src_genv_nb)). *)

  Definition inv_sat_blk blk (invar: memblk_invariant) (m: mem): Prop :=
    invar (fun chunk ofs =>
             if (Mem.valid_access_dec m chunk blk ofs Writable)
             then Mem.load chunk m blk ofs
             else None).

  (* Definition inv_sat_mem (invar: memory_invariant) (m: mem) : Prop := *)
  (*   forall blk inv_blk (INVAR: invar blk inv_blk), inv_sat_blk blk inv_blk m.   *)

  Definition inv_sat_mem (invar: block -> Prop) (m: mem) : Prop :=
    forall blk (INVAR: invar blk), inv_sat_blk blk P m.

  Inductive wf' (sm0: t'): Prop :=
  | wf_intro
      (WF: Mem.inject sm0.(inj) sm0.(src) sm0.(tgt))
      (SAT: inv_sat_mem sm0.(mem_inv) sm0.(tgt))
      (INVRANGE: forall blk ofs (INV: sm0.(mem_inv) blk),
          loc_out_of_reach sm0.(inj) sm0.(src) blk ofs /\ Mem.valid_block sm0.(tgt) blk)
      (* (INVRANGE: forall blk ofs invar (INV: sm0.(mem_inv) blk invar),         *)
      (*     loc_out_of_reach sm0.(inj) sm0.(src) blk ofs /\ Mem.valid_block sm0.(tgt) blk) *)
  .

  Lemma unchanged_on_invariant invar m0 m1
        (INVAR: inv_sat_mem invar m0)
        (INVRANGE: invar <1= Mem.valid_block m0)
        (UNCH: Mem.unchanged_on (fun blk _ => invar blk) m0 m1)
    :
      inv_sat_mem invar m1.
  Proof.
    ii. exploit INVAR; eauto. intros SAT.
    unfold inv_sat_blk in *. rp; eauto.
    extensionality chunk. extensionality ofs.
    des_ifs.
    - eapply Mem.load_unchanged_on_1; eauto.
    - exfalso. apply n. inv v. split; auto.
      ii. eapply Mem.perm_unchanged_on_2; eauto.
    - exfalso. apply n. inv v. split; auto.
      ii. eapply Mem.perm_unchanged_on; eauto.
  Qed.

  Inductive le' (mrel0 mrel1: t'): Prop :=
  | le_intro
      (SRCNBLE: Ple mrel0.(src).(Mem.nextblock) mrel1.(src).(Mem.nextblock))
      (TGTNBLE: Ple mrel0.(tgt).(Mem.nextblock) mrel1.(tgt).(Mem.nextblock))
      (INCR: inject_incr mrel0.(inj) mrel1.(inj))
      (FROZEN: inject_separated
               (mrel0.(inj)) (mrel1.(inj))
               (mrel0.(src)) (mrel0.(tgt)))
      (MINVEQ: mrel0.(mem_inv) = mrel1.(mem_inv))
  .

  (* "Global" is needed as it is inside section *)
  Global Program Instance SimMemInjInv : SimMem.class :=
    {
      t := t';
      src := src;
      tgt := tgt;
      wf := wf';
      le := le';
      lift := fun sm => sm;
      unlift := fun _ sm => sm;
      sim_val := fun (mrel: t') => Val.inject mrel.(inj);
      sim_val_list := fun (mrel: t') => Val.inject_list mrel.(inj);
    }.
  Next Obligation.
    econs.
    - econs; ss.
      + refl.
      + refl.
      + ii. clarify.
    - ii. inv H. inv H0. econs; eauto.
      + etrans; eauto.
      + etrans; eauto.
      + etrans; eauto.
      + ii. destruct (inj y b1) as [[b3 delta0]|] eqn:DELTA.
        * dup DELTA. eapply INCR0 in DELTA. clarify.
          exploit FROZEN; eauto.
        * dup DELTA. exploit FROZEN0; eauto. i. des.
          unfold Mem.valid_block in *. split; ii.
          { eapply H1. eapply Plt_Ple_trans; eauto. }
          { eapply H2. eapply Plt_Ple_trans; eauto. }
      + etrans; eauto.
  Qed.
  Next Obligation.
    inv MLE. ii. eapply val_inject_incr; eauto.
  Qed.
  Next Obligation.
    extensionality l0. extensionality l1. eapply prop_ext2.
    induction x0; ss; i; split; intros H; inv H; econs; eauto.
    - eapply IHx0; eauto.
    - eapply IHx0; eauto.
  Qed.

  Lemma mem_inv_le sm0 sm1
        (MLE: le' sm0 sm1)
    :
      sm0.(mem_inv) <1= sm1.(mem_inv).
  Proof.
    inv MLE. rewrite MINVEQ. auto.
  Qed.

End MEMINJINV.


Section SIMSYMBINV.

  Variable P : memblk_invariant.

  Inductive le (ss0: ident -> Prop) (sk_src sk_tgt: Sk.t) (ss1: ident -> Prop): Prop :=
  | symb_le_intro
      (LE: ss0 <1= ss1)
      (OUTSIDE: forall
          id
          (IN: (ss1 -1 ss0) id)
        ,
          <<OUTSIDESRC: ~ sk_src.(defs) id>> /\ <<OUTSIDETGT: ~ sk_tgt.(defs) id>>)
  .

  Inductive skenv_inject {F V} (ge: Genv.t F V) (j: meminj)
            (invar: block -> Prop) : Prop :=
  | sken_inject_intro
      (DOMAIN: forall b, Plt b ge.(Genv.genv_next) ->
                         forall (NINV: ~ invar b), j b = Some(b, 0))
      (NDOMAIN: forall b, Plt b ge.(Genv.genv_next) ->
                          forall (NINV: invar b), j b = None)
      (IMAGE: forall b1 b2 delta, j b1 = Some(b2, delta) -> Plt b2 ge.(Genv.genv_next) -> b1 = b2)
  .

  Inductive invariant_globvar F V: globdef F V -> Prop :=
  | invariant_globvar_intro
      v
      (INITD: admit "about init data" v.(gvar_init))
    :
      invariant_globvar (Gvar v)
  .

  Inductive sim_skenv_inj (sm: t') (ss: ident -> Prop) (skenv_src skenv_tgt: SkEnv.t): Prop :=
  | sim_skenv_inj_intro
      (INVCOMPAT: forall id blk (FIND: skenv_tgt.(Genv.find_symbol) id = Some blk),
          ss id <-> sm.(mem_inv) blk)
      (PUBKEPT: (fun id => In id skenv_src.(Genv.genv_public)) <1= ~1 ss)
      (INJECT: skenv_inject skenv_src sm.(inj) sm.(mem_inv))
      (BOUNDSRC: Ple skenv_src.(Genv.genv_next) sm.(src).(Mem.nextblock))
      (BOUNDTGT: Ple skenv_src.(Genv.genv_next) sm.(tgt).(Mem.nextblock))
      (SIMSKENV: SimSymbId.sim_skenv skenv_src skenv_tgt)
  .

  Inductive sim_sk (ss: ident -> Prop) (sk_src sk_tgt: Sk.t): Prop :=
  | sim_sk_intro
      (SKSAME: sk_src = sk_tgt)
      (CLOSED: forall id (SS: ss id),
          exists g,
            (<<DEF: sk_tgt.(prog_defmap) ! id = Some g>>) /\
            (<<INV: invariant_globvar g>>) /\
            (<<PRVT: ~ In id (prog_public sk_tgt)>>)).

  Global Program Instance SimSymbIdInv: SimSymb.class (SimMemInjInv P) :=
    {
      t := ident -> Prop;
      le := le;
      sim_sk := sim_sk;
      sim_skenv := sim_skenv_inj;
    }
  .
  Next Obligation.
    econs; eauto. i. des. clarify.
  Qed.
  Next Obligation.
    admit "ez - copy SimSymbDrop".
  Qed.
  Next Obligation.
    inv SIMSK. eauto.
  Qed.
  Next Obligation.
    inv SIMSK. inv SIMSK0. exists (ss0 \1/ ss1).
    admit "copy SimSymbDrop".
  Qed.
  Next Obligation.
    inv SIMSKE. inv SIMSKENV. eauto.
  Qed.
  Next Obligation.
    inv SIMSK. eexists.
    assert (SS: forall id, {ss id} + {~ ss id}).
    { admit "choice + classic". }
    set (j := fun blk => if (plt blk (Mem.nextblock m_src))
                         then match Genv.invert_symbol (Sk.load_skenv sk_tgt) blk with
                              | Some id =>
                                if (SS id) then None else Some (blk, 0)
                              | None => None
                              end
                         else None).
    eexists (mk _ _ j _). ss.
    instantiate (1:=fun blk => exists id,
                        (<<FIND: (Sk.load_skenv sk_tgt).(Genv.find_symbol) id = Some blk>>) /\
                        (<<SINV: ss id>>)).
    esplits; eauto.
    - econs; ss; eauto.
      + i. split; i; eauto. des.
        apply Genv.find_invert_symbol in FIND.
        apply Genv.find_invert_symbol in H. clarify.
      + ii. exploit CLOSED; eauto. i. des.
        apply PRVT. rewrite <- Genv.globalenv_public. auto.
      + admit "".
      + unfold Sk.load_mem in *.
        apply Genv.init_mem_genv_next in LOADMEMSRC.
        rewrite <- LOADMEMSRC. refl.
      + unfold Sk.load_mem in *.
        apply Genv.init_mem_genv_next in LOADMEMSRC.
        rewrite <- LOADMEMSRC. refl.

    - econs; ss; eauto.
      + admit "copy SimSymbId".
        (* econs; ss; eauto. *)
        (* * *)
        (*   econs; eauto; ii; unfold j in *; des_ifs; clarify. *)
        (*   { zsimpl. auto. } *)
        (*   { apply Z.divide_0_r. } *)
        (*   { zsimpl. admit "TODO". } *)
        (* * ii. unfold j. des_ifs. *)
        (* * ii. unfold j in *. des_ifs. *)
        (* * ii. unfold j in *. des_ifs. auto. *)
        (* * ii. unfold j in *. des_ifs. *)
        (*   admit "TODO". *)
      + admit "fill invariant_globvar".
      + i. split.
        * unfold j. ii. des_ifs.
          des. eapply Genv.find_invert_symbol in INV. clarify.
        * des. eapply Genv.genv_symb_range in INV.
          unfold Sk.load_skenv, Sk.load_mem in *. ss.
          apply Genv.init_mem_genv_next in LOADMEMSRC.
          rewrite LOADMEMSRC in *. auto.
  Qed.
  Next Obligation.
  Admitted.
  (*   destruct sm0, sm1. inv MLE. ss. clarify. *)
  (*   inv SIMSKENV. econs; ss; eauto. *)
  (*   - inv INJECT. econs; eauto. *)
  (*     + i. destruct (inj minj1 b) eqn:BLK; auto. destruct p. exfalso. *)
  (*       inv FROZEN. exploit NEW_IMPLIES_OUTSIDE; eauto. *)
  (*       i. des. eapply Plt_strict. eapply Plt_Ple_trans. *)
  (*       * apply H. *)
  (*       * transitivity (src_parent_nb minj0); eauto. *)
  (*     + i. destruct (inj minj0 b1) eqn:BLK. *)
  (*       * destruct p. dup BLK. apply INCR in BLK. clarify. *)
  (*         eapply IMAGE; eauto. *)
  (*       * inv FROZEN. exploit NEW_IMPLIES_OUTSIDE; eauto. *)
  (*         i. des. exfalso. eapply Plt_strict. eapply Plt_Ple_trans. *)
  (*         { apply H0. } *)
  (*         { etrans; eauto. } *)
  (*   - rewrite <- SRCPARENTEQNB. auto. *)
  (*   - rewrite <- TGTPARENTEQNB. auto. *)
  (* Qed. *)
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
    inv SIMSKENV. inv SIMSKENV0.
    inv ARGS. inv MWF. ss.
    exploit ec_mem_inject; eauto.
    - eapply external_call_spec.
    - instantiate (1:=skenv_sys_tgt).
      inv INJECT. econs; ss. splits.
      + i. destruct (classic (mem_inv sm0 b1)).
        { exfalso. eapply NDOMAIN in H1.
          - clarify.
          - eapply Genv.genv_symb_range; eauto. }
        exploit DOMAIN; eauto.
        { eapply Genv.genv_symb_range; eauto. }
        i. clarify.
      + i. exploit DOMAIN; eauto.
        * eapply Genv.genv_symb_range; eauto.
        * ii. eapply INVCOMPAT in H1; eauto.
          eapply PUBKEPT; eauto.
          unfold Genv.public_symbol, proj_sumbool in *. des_ifs.
      + i. destruct (Genv.block_is_volatile skenv_sys_tgt b1) eqn:VOL1.
        * dup VOL1. eapply Genv.block_is_volatile_below in VOL1.
          destruct (classic (mem_inv sm0 b1)).
          { exfalso. hexploit NDOMAIN; eauto. i. clarify. }
          { hexploit DOMAIN; eauto. i. clarify. }
        * destruct (Genv.block_is_volatile skenv_sys_tgt b2) eqn:VOL2; auto.
          dup VOL2. eapply Genv.block_is_volatile_below in VOL2.
          exfalso. exploit IMAGE; eauto. i. clarify.
    - rewrite MEMSRC. eauto.
    - i. des. eexists (mk _ _ _ _). exists (Retv.mk vres' m2'). ss.
      esplits; ss; eauto.
      + rewrite MEMTGT. eauto.
      + econs; ss; eauto.
      + econs; ss; eauto.
        * rewrite MEMSRC in *. eapply Mem.unchanged_on_nextblock; eauto.
        * eapply Mem.unchanged_on_nextblock; eauto.
        * rewrite MEMSRC in *. eauto.
      + econs; ss; eauto.
        * eapply unchanged_on_invariant; eauto.
          { ii. eapply INVRANGE; eauto. apply 0. }
          { eapply Mem.unchanged_on_implies; eauto.
            i. rewrite MEMSRC. eapply INVRANGE; eauto. }
        * ii. exploit INVRANGE; eauto. i. des. split.
          { ii. eapply H6; eauto.
            - instantiate (1:=delta). instantiate (1:=b0).
              destruct (inj sm0 b0) as [[blk0 delta0]|] eqn:DELTA.
              + eapply H4 in DELTA. clarify.
              + exfalso. exploit H5; eauto. i. des. clarify.
            - rewrite MEMSRC in *. eapply external_call_max_perm; eauto.
              destruct (inj sm0 b0) as [[blk0 delta0]|] eqn:DELTA.
              + dup DELTA. eapply H4 in DELTA. clarify.
                eapply Mem.valid_block_inject_1; eauto.
              + exfalso. exploit H5; eauto. i. des. clarify. }
          { eapply Plt_Ple_trans; eauto.
            eapply Mem.unchanged_on_nextblock; eauto. }
  Qed.

End SIMSYMBINV.
