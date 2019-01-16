Require Import Events.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
From Paco Require Import paco.
Require Import sflib.
Require Import Skeleton.
Require Import CoqlibC.
Require Import Simulation.
Require Import ModSem.

Set Implicit Arguments.



Lemma spread_dstar
      ms
      st0 tr st1
      (DTM: forall st0, determinate_at ms st0)
      (STAR: Star ms st0 tr st1)
  :
    <<DSTAR: DStar ms st0 tr st1>>
.
Proof.
  ginduction STAR; ii; ss.
  { econs; eauto. }
  econs; eauto. eapply IHSTAR; eauto.
Qed.

Lemma spread_dplus
      ms
      st0 tr st1
      (DTM: forall st0, determinate_at ms st0)
      (PLUS: Plus ms st0 tr st1)
  :
    <<DPLUS: DPlus ms st0 tr st1>>
.
Proof.
  inv PLUS. econs; eauto. eapply spread_dstar; eauto.
Qed.

Lemma at_external_receptive_at
      ms_src lst_src
      (CALL: ModSem.is_call ms_src lst_src)
  :
    <<RCP: receptive_at ms_src lst_src>>
.
Proof.
  econs; ii; ModSem.tac.
Qed.

Lemma at_external_determinate_at
      ms_src lst_src
      (CALL: ModSem.is_call ms_src lst_src)
  :
    <<RCP: determinate_at ms_src lst_src>>
.
Proof.
  econs; ii; ModSem.tac.
Qed.

Lemma final_frame_receptive_at
      ms_src lst_src
      (CALL: ModSem.is_return ms_src lst_src)
  :
    <<RCP: receptive_at ms_src lst_src>>
.
Proof.
  econs; ii; ModSem.tac.
Qed.

Lemma final_frame_determinate_at
      ms_src lst_src
      (CALL: ModSem.is_return ms_src lst_src)
  :
    <<RCP: determinate_at ms_src lst_src>>
.
Proof.
  econs; ii; ModSem.tac.
Qed.
