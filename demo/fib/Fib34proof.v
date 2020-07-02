Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC MemoryC GlobalenvsC Events Smallstep.
Require Import Op ClightC.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSemLift SimSymb SimMemLift MatchSimModSemExcl.
Require SoundTop.
Require SimMemId.
Require Import Any.
Require Import SIR.
Require Import SIRStack.
Require Import Fib4.
Require Import Fib3.
Require Import ModSemProps.
Require Import Program.
Require Import SIRProps.
Require Import ITreelib.
From Coq Require Import
     Morphisms RelationClasses.
(*** TODO: export in in SIRCommon or somewhere ***)

Set Implicit Arguments.

(* Ltac step := gstep; econs; et. *)
Ltac step_unwrapN := match goal with
                     | |- context[unwrapN ?ox ;; _] =>
                       (*** I want to unfold only the "first" assume.
Maybe we should use notation instead, so that we can avoid this weird "unfold"? ***)
                       first[
                           unfold unwrapN at 5|
                           unfold unwrapN at 4|
                           unfold unwrapN at 3|
                           unfold unwrapN at 2|
                           unfold unwrapN at 1|
                           unfold unwrapN at 0
                         ];
                       let name := fresh "T" in
                       destruct ox eqn:name; cycle 1
                     end
.

Hint Rewrite unfold_interp_mrec : itree_axiom2.
Hint Rewrite bind_ret_l : itree_axiom2.
Hint Rewrite bind_ret_r : itree_axiom2.
Hint Rewrite bind_tau : itree_axiom2.
Hint Rewrite bind_vis : itree_axiom2.
(* Hint Rewrite bind_trigger : itree_axiom2. *) (********* <---------removed this ***********)
Hint Rewrite bind_bind : itree_axiom2.
Tactic Notation "irw" "in" ident(H) := repeat (autorewrite with itree_axiom2 in H; cbn in H).
Tactic Notation "irw" := repeat (autorewrite with itree_axiom2; cbn).


Definition option_rel A B (r: A -> B -> Prop): option A -> option B -> Prop :=
  fun oa ob =>
    match oa, ob with
    | Some a, Some b => <<REL: r a b>>
    | None, None => True
    | _, _ => False
    end
.

Definition mp: ModPair.t := SimSymbId.mk_mp (Fib4.module) (Fib3.module).
Theorem sim_mod: ModPair.sim mp.
Proof.
  assert(tau: forall E R (a: itree E R), (tau;; a) = a).
  { admit "backdoor --- relax sim_st to allow tau* before each progress". }
  eapply (SIRHoareproof.sim_mod).
  instantiate (1:= postcond).
  instantiate (1:= precond).
  instantiate (1:= _fib_ru).
  instantiate (1:= Fib0._fib).
  econs; ss; et.
  - econs; ss; cycle 1.
    + unfold f_fib.
      eapply func_ext3. ii.
      rewrite tau.
      rewrite bind_bind.
      refl.
    + ii. clarify. unfold f_fib_ru. rewrite tau.
      replace Fib4.parse_arg with parse_arg by ss.
      pfold. step_unwrapN.
      { cbn. des_ifs_safe.
        unfold triggerNB. irw. econs; et. }
      destruct n.
      { irw. econs; ss; et. }
      destruct n.
      { irw. econs; ss; et. }
      cbn. rewrite ! bind_ret_l. irw.
      erewrite f_equal; try eapply match_icall_fn; cycle 1.
      { f. f_equiv. ii. f_equiv. ii. des_ifs_safe. f_equiv. ii. f.
        instantiate (1:= fun '(oh, (m, v)) => _). refl. }
      ii. des_ifs_safe. left.
      pfold.
      erewrite f_equal; try eapply match_icall_fn; cycle 1.
      { f. f_equiv. ii. f_equiv. ii. des_ifs_safe. f_equiv. ii. f.
        instantiate (1:= fun '(oh, (m, v)) => _). refl. }
      ii. des_ifs_safe. left. pfold. econs; et.
  - ii. replace Coqlib.option_rel with option_rel; cycle 1.
    { admit "change the definition itself". }
    Local Opaque ident_eq.
    r. unfold Fib4.prog, prog. ss. des_ifs; ss.
Qed.

Require Import RUSC AdequacyLocal IdSimExtra.

Let rel_default := (mkPR SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top).
Theorem eutt_proof
        owned_heap
        (p_src p_tgt: program owned_heap)
        (SIM: (eq ==> (option_rel (eq ==> eq ==> eq ==> eutt eq)))%signature p_src p_tgt)
        sk mi init_oh
  :
    rusc (eq rel_default) [SIR.module sk p_src mi init_oh]
         [SIR.module sk p_tgt mi init_oh]
.
Proof.
Admitted.

Theorem rusc_format
  :
    rusc (eq rel_default) [Fib4.module] [Fib3.module]
.
Proof.
  unfold Fib4.module, Fib3.module.
  rewrite eutt_proof; cycle 1.
  { ii. clarify. unfold Fib4.prog.
    instantiate (1:= (add _fib_ru (fun _ _ _ => _) (add Fib0._fib (fun _ _ _ => _) empty))).
    ss. des_ifs.
    - ii. clarify. unfold f_fib_ru. rewrite tau_eutt. refl.
    - ii. clarify. refl.
  }
  eapply (@relate_single_rusc (eq rel_default) SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top).
  - ii. exists mp. esplits; ss; et. eapply sim_mod.
  - ss.
Qed.
