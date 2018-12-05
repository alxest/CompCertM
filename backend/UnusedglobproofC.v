Require Import FSets CoqlibC Maps Ordered Iteration Errors.
Require Import AST Linking.
Require Import IntegersC ValuesC Memory Globalenvs Events Smallstep.
Require Import Op Registers RTLC.
Require Import Unusedglob.
Require Import sflib.
Require SimMemInj.
(** newly added **)
Require Export Unusedglobproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemInjC.
Require SimSymbDrop.
Require SoundTop.
Require Import CtypingC.
Require Import ModSemProps.

Set Implicit Arguments.
Local Existing Instance Val.mi_normal.






Definition from_list (ids: list ident): IS.t :=
  fold_right (fun i s => IS.add i s) IS.empty ids
.

Lemma from_list_spec
      x xs
  :
    IS.In x (from_list xs) <-> In x xs
.
Proof.
  unfold from_list.
  split; i.
  - ginduction xs; ii; ss.
    { rewrite ISF.empty_iff in *. ss. }
    rewrite ISF.add_iff in *. des; et.
  - ginduction xs; ii; ss.
    rewrite ISF.add_iff in *. des; et.
Qed.

Fixpoint list_diff X (dec: (forall x0 x1, {x0 = x1} + {x0 <> x1})) (xs0 xs1: list X): list X :=
  match xs0 with
  | [] => []
  | hd :: tl =>
    if in_dec dec hd xs1
    then list_diff dec tl xs1
    else hd :: list_diff dec tl xs1
  end
.

Lemma list_diff_spec
      X dec (xs0 xs1 xs2: list X)
      (DIFF: list_diff dec xs0 xs1 = xs2)
  :
    <<SPEC: forall x0, In x0 xs2 <-> (In x0 xs0 /\ ~ In x0 xs1)>>
.
Proof.
  subst.
  split; i.
  - ginduction xs0; ii; des; ss.
    des_ifs.
    { exploit IHxs0; et. i; des. esplits; et. }
    ss. des; clarify.
    { tauto. }
    exploit IHxs0; et. i; des. esplits; et.
  - ginduction xs0; ii; des; ss.
    des; clarify; des_ifs; ss; try tauto.
    { exploit IHxs0; et. }
    { exploit IHxs0; et. }
Qed.





Section SIMMODSEM.

Variable skenv_link_src skenv_link_tgt: SkEnv.t.
Variable sm_link: SimMem.t.
Hypothesis (SIMSKENVLINK: exists ss_link, SimSymb.sim_skenv sm_link ss_link skenv_link_src skenv_link_tgt).
Variable prog: RTL.program.
Variable tprog: RTL.program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge: RTL.genv := (SkEnv.revive (SkEnv.project skenv_link_src (defs prog)) prog).
Let tge: RTL.genv := (SkEnv.revive (SkEnv.project skenv_link_tgt (defs tprog)) tprog).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (RTLC.modsem skenv_link_src prog) (RTLC.modsem skenv_link_tgt tprog)
                ((prog.(defs) -1 tprog.(defs)): ident -> Prop) sm_link
.

(* Definition used: IS.t := from_list (prog.(prog_defmap).(PTree.elements)) *)

Definition used: IS.t :=
  (* from_list (list_diff Pos.eq_dec (prog.(prog_defs_names)) (tprog.(prog_defs_names))) *)
  from_list (tprog.(prog_defs_names))
.

(* Lemma used_spec *)
(*       id *)
(*   : *)
(*     <<KEPT: kept used id>> <-> <<SPEC: ~ (defs prog id /\ ~ defs tprog id)>> *)
(* . *)
(* Proof. *)
(*   unfold used, kept. ss. *)
(*   split; i; r; des. *)
(*   - rewrite from_list_spec in *. *)
(*     ii. des. *)
(*     unfold defs in *. des_sumbool. *)
(*     apply H1. des_sumbool. ss. *)
(*   - rewrite from_list_spec in *. *)
(*     apply not_and_or in H. des; ss. *)
(*     { admit "". } *)
(*     apply NNPP in H. *)
(*     unfold defs in *. des_sumbool. ss. *)
(* Qed. *)

Lemma used_spec
      id
  :
    <<KEPT: kept used id>> <-> <<SPEC: defs tprog id>>
.
Proof.
  unfold used, kept. ss.
  unfold defs. unfold NW.
  split; i; r; des.
  - rewrite from_list_spec in *.
    des_sumbool. ss.
  - rewrite from_list_spec in *.
    des_sumbool. ss.
Qed.

(* Definition used': option IS.t := used_globals prog (prog_defmap prog). *)

(* Lemma used'_spec *)
(*       id *)
(*       used'' *)
(*       (SOME: used' = Some used'') *)
(*   : *)
(*     <<KEPT: kept used'' id>> <-> <<SPEC: defs tprog id>> *)
(* . *)
(* Proof. *)
(*   unfold used', kept in *. ss. *)
(*   unfold defs. unfold NW. *)
(*   split; i; r; des. *)
(*   - rewrite from_list_spec in *. *)
(*     des_sumbool. ss. *)
(*   - rewrite from_list_spec in *. *)
(*     des_sumbool. ss. *)
(* Qed. *)

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: RTL.state) (st_tgt0: RTL.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: Unusedglobproof.match_states prog tprog used ge tge st_src0 st_tgt0 sm0)
    (MCOMPATSRC: st_src0.(RTLC.get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(RTLC.get_mem) = sm0.(SimMem.tgt))
.

(* Theorem make_match_genvs : *)
(*   SimSymbId.sim_skenv (SkEnv.project skenv_link_src (defs prog)) (SkEnv.project skenv_link_tgt (defs tprog)) -> *)
(*   Genv.match_genvs (match_globdef (fun _ f tf => tf = transf_fundef f) eq prog) ge tge. *)
(* Proof. subst_locals. eapply SimSymbId.sim_skenv_revive; eauto. { ii. clarify. u. des_ifs. } Qed. *)

(* Theorem make_match_genvs : *)
(*   SimSymbId.sim_skenv (SkEnv.project skenv_link_src (defs prog)) (SkEnv.project skenv_link_tgt (defs tprog)) -> *)
(*   Genv.match_genvs (match_globdef (fun (ctx: AST.program fundef type) f tf => transf_fundef f = OK tf) eq prog) ge tge /\ prog_comp_env prog = prog_comp_env tprog. *)
(* Proof. *)
(*   subst_locals. ss. *)
(*   rr in TRANSL. destruct TRANSL. r in H. *)
(*   esplits. *)
(*   - eapply SimSymbId.sim_skenv_revive; eauto. *)
(*     { ii. u. unfold transf_fundef, bind in MATCH. des_ifs; ss; clarify. } *)
(*   - hexploit (prog_comp_env_eq prog); eauto. i. *)
(*     hexploit (prog_comp_env_eq tprog); eauto. i. *)
(*     ss. congruence. *)
(* Qed. *)

Lemma find_funct_inject
      fptr tfptr fd j
      (SIMGE: meminj_preserves_globals prog tprog used ge tge j)
      (FINDSRC: Genv.find_funct ge fptr = Some fd)
      (INJ: Val.inject j fptr tfptr)
  :
    <<FINDTGT: Genv.find_funct tge tfptr = Some fd>>
.
Proof.
  inv SIMGE.
  uge0. des_ifs_safe.
  inv INJ.
  exploit defs_inject; et. i; des. clarify. psimpl. des_ifs.
Qed.

Theorem sim_skenv_meminj_preserves_globals
        sm_arg
        (SIMSKENV: SimSymbDrop.sim_skenv
                     sm_arg ((prog.(defs) -1 tprog.(defs)): ident -> Prop)
                     (SkEnv.project skenv_link_src (defs prog)) (SkEnv.project skenv_link_tgt (defs tprog)))
  :
    <<SIMGE: meminj_preserves_globals prog tprog used ge tge (SimMemInj.inj sm_arg)>>
.
Proof.
  inv SIMSKENV. ss. bar.
  econs.
  - i. exploit SIMSYMB1; et. i; des. clarify.
  - i. exploit SIMSYMB2; et.
    { hexploit (used_spec id); et. i; des. tauto. }
  - eauto.
  - i. unfold ge in H0. exploit Genv_map_defs_def; et. i; des.
    exploit SIMDEF; et. i; des. clarify. psimpl.
    Ltac uo := unfold o_bind, o_map, o_join in *.
    uo. des_ifs_safe.
    exploit Genv.invert_find_symbol; et. intro SYMBSRC; des.
    exploit SIMSYMB1; et. i; des. psimpl. clear_tac. 
    exploit Genv.find_invert_symbol; et. intro SYMBTGT; des.
    apply not_and_or in KEPT.
    des; ss.
    { clear - Heq1 KEPT. contradict KEPT. unfold defs in *. des_sumbool. apply prog_defmap_spec; et. }
    apply NNPP in KEPT.
    destruct TRANSL as [used0 TRANSL0]. des.
    assert(used0 = used).
    { admit "Identify Used !!". }
    clarify.
    assert(IN: IS.In i used).
    { unfold used. apply from_list_spec. unfold defs in *. ss. des_sumbool. ss. }
    esplits; et.
    + unfold tge.
      unfold SkEnv.revive.
      erewrite Genv_map_defs_def_inv; et.
      uo. des_ifs_safe.
      erewrite match_prog_def; et. des_ifs.
      exploit IS.mem_1; et. i; clarify.
    + i. eapply used_closed; et.
  - unfold tge. i.
    exploit Genv_map_defs_def; et. i; des.
    uo. des_ifs. bsimpl.
    exploit SIMDEFINV; et. i; des. clarify. psimpl. clear_tac.
    exploit Genv.invert_find_symbol; et. intro SYMBTGT; des.
    exploit SIMSYMB3; et. i; des.
    exploit Genv.find_invert_symbol; et. intro SYMBSRC.
    esplits; et.

    assert(kept used i).
    { apply used_spec. u. des_sumbool. apply prog_defmap_spec; et. }

    exploit SIMSYMB2; et.
    { apply used_spec in H1. tauto. }
    i; des.
    clarify. clear_tac.

    assert(blk_src = b).
    { eapply DISJ; et. }
    clarify.


    unfold ge.
    unfold SkEnv.revive.
    erewrite Genv_map_defs_def_inv; et.
    uo.
    des_ifs_safe.

    destruct TRANSL as [used0 TRANSL0]. des.
    hexploit (match_prog_def _ _ _ TRANSL1 i); et. intro DEFMAP. des_ifs.
  - eauto.
Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  (* rr in TRANSL. destruct TRANSL as [TRANSL0 TRANSL1]. *)
  eapply match_states_sim with (match_states := match_states)
                               (match_states_at := fun _ _ => eq)
                               (sound_state := SoundTop.sound_state);
    eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    (* destruct sm_arg; ss. clarify. *)
    destruct args_src, args_tgt; ss.
    inv SIMARGS; ss. clarify.
    inv INITTGT. ss.
    (* hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des. *)
    (* exploit make_match_genvs; eauto. { inv SIMSKENV. ss. } intro SIMGE. des. *)
    assert(SIMGE: meminj_preserves_globals prog tprog used ge tge (SimMemInj.inj sm_arg)).
    { eapply sim_skenv_meminj_preserves_globals; et. }
    des.
    eexists. exists sm_arg.
    esplits; eauto.
    { refl. }
    + econs; eauto; ss; cycle 1.
      { inv SAFESRC. ss. }
      * inv TYP.
        inv SAFESRC. folder. ss.


        inv TYP.
        exploit find_funct_inject; et. i; des. clarify.
        rpapply match_states_call; ss; eauto.
        { econs; ss; et.
          admit "ez - genb".
          admit "ez - genb".
        }
        {
          admit "ez".
        }
        { eapply MWF. }
  - des. inv SAFESRC.
    inv SIMARGS; ss.
    (* hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des. *)
    (* exploit make_match_genvs; eauto. { inv SIMSKENV. ss. } intro SIMGE. des. *)
    assert(SIMGE: meminj_preserves_globals prog tprog used ge tge (SimMemInj.inj sm_arg)).
    { eapply sim_skenv_meminj_preserves_globals; et. }
    exploit find_funct_inject; et. i; des. clarify.
    (* exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify. folder. *)
    (* hexploit (@sim_external_inject_eq_fsim); try apply FINDF; eauto. clear FPTR. intro FPTR. *)
    (* unfold transf_function, bind in *. des_ifs. *)
    (* unfold bind in *. des_ifs. *)
    inv TYP.
    esplits; eauto. econs; eauto.
    + (* TODO: add lemma *)
      econs; et.
      etrans; try apply LEN; et. symmetry. eapply inject_list_length; et.
    + etrans; try apply LEN; et. symmetry. eapply inject_list_length; et.
  - (* call wf *)
    inv MATCH; ss. inv MATCHST; ss.
  - (* call fsim *)
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { inv SIMSKENV. ss. } intro SIMGE. des.
    inv MATCH; ss. destruct sm0; ss. clarify.
    inv CALLSRC. inv MATCHST; ss.
    folder.
    inv MCOMPAT; ss. clear_tac.
    exploit (sim_external_funct_inject SIMGE); eauto. { ii; clarify; ss. des; ss. } intro EXTTGT.
    esplits; eauto.
    + econs; eauto.
      * des. clarify. esplits; eauto.
        (* exploit (sim_internal_funct_inject SIMGE); try apply SIG; et. *)

        (* Arguments sim_internal_funct_inject [_]. *)
        (* destruct SIMSKENVLINK. inv H.  rr in SIMSKENV1. clarify. *)
        (* exploit (sim_internal_funct_inject); try apply VAL; try apply SIG; et. *)
        (* { erewrite match_globdef_eq. eapply Global_match_genvs_refl. } *)
        (* { inv SIMSKENV. ss. } *)

        (***************** TODO: Add as a lemma in GlobalenvsC. *******************)
        destruct SIMSKENVLINK.
        assert(fptr_arg = tv).
        { eapply sim_external_inject_eq_fsim; try apply SIG; et. Undo 1.
          inv VAL; ss. des_ifs_safe. apply Genv.find_funct_ptr_iff in SIG. unfold Genv.find_def in *.
          inv SIMSKENV; ss. inv INJECT; ss.
          exploit (DOMAIN b1); eauto.
          { eapply Genv.genv_defs_range; et. }
          i; clarify.
        }
        clarify.
        eapply SimSymb.simskenv_func_fsim; eauto; ss.
        { destruct tv; ss. des_ifs. econs; eauto; cycle 1.
          { psimpl. instantiate (1:= 0). ss. }
          inv H. inv INJECT. eapply DOMAIN; eauto.
          { apply Genv.find_funct_ptr_iff in SIG. unfold Genv.find_def in *. eapply Genv.genv_defs_range; et. }
        }
    + ss.
    + reflexivity.
  - (* after fsim *)
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { inv SIMSKENV. ss. } intro SIMGE. des.
    inv AFTERSRC.
    inv SIMRET. ss. exists (SimMemInj.unlift' sm_arg sm_ret). destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss.
    inv HISTORY. ss. clear_tac.
    esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto. destruct retv_src, retv_tgt; ss. clarify.
      inv MLE0; ss.
      inv MCOMPAT. clear_tac.
      rpapply match_return_state; ss; eauto; ss.
      (* { clear - MWF. inv MWF. ii. apply TGTEXT in H. rr in H. des. ss. } *)
      { ss. ii.
        eapply match_cont_incr_bounds; eauto; swap 2 4.
        { instantiate (1:= tge). ss. esplits; eauto. }
        { eauto with mem. }
        { eauto with mem. }
        eapply match_cont_extcall; eauto.
        { instantiate (1:= tge). ss. esplits; eauto. }
        { eapply Mem.unchanged_on_implies; try eassumption. ii. rr. esplits; eauto. }
        { eapply SimMemInj.inject_separated_frozen; et. }
        { refl. }
        { refl. }
      }
      { eapply MWFAFTR. }
      { eapply typify_inject; et. }
    + refl.
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss.
    inv MCONT_EXT. inv MCOMPAT; ss.
    eexists sm0. esplits; ss; eauto. refl.
  - exploit make_match_genvs; eauto. { inv SIMSKENV. ss. } intro SIMGE. des.

    esplits; eauto.
    { apply modsem1_receptive. }
    inv MATCH.
    ii. hexploit (@step_simulation prog ge tge); eauto.
    i; des.
    esplits; eauto.
    + left. eapply spread_dplus; eauto. eapply modsem2_determinate; eauto.
    + econs; ss.
      * inv H0; ss; inv MCOMPAT; ss.
      * inv H0; ss; inv MCOMPAT; ss.
Unshelve.
  all: ss; try (by econs).
Qed.

End SIMMODSEM.


Section SIMMOD.

Variable prog: Clight.program.
Variable tprog: Clight.program.
Hypothesis TRANSL: match_prog prog tprog.

Definition mp: ModPair.t :=
  ModPair.mk (ClightC.module1 prog) (ClightC.module2 tprog) tt
.

Theorem sim_mod
  :
    ModPair.sim mp
.
Proof.
  econs; ss.
  - r. admit "easy - see DeadcodeproofC".
  - ii. eapply sim_modsem; eauto.
Unshelve.
  all: ss.
Qed.

End SIMMOD.

