Require Import CoqlibC.
Require Import Memory.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import sflib.
Require Import RelationClasses.
Require Import FSets.
Require Import Ordered.
Require Import AST.
Require Import Integers.

Require Import Sem ModSem.

Set Implicit Arguments.






Module SimMem.

  Class class :=
  { t: Type;
    src: t -> mem;
    tgt: t -> mem;
    wf: t -> Prop;
    le: t -> t -> Prop;
    lepriv: t -> t -> Prop;

    le_PreOrder :> PreOrder le;
    lepriv_PreOrder :> PreOrder lepriv;

    pub_priv: forall sm0 sm1, le sm0 sm1 -> lepriv sm0 sm1;

    sim_val: t -> val -> val -> Prop;
    sim_val_list: t -> list val -> list val -> Prop;
    le_sim_val: forall mrel0 mrel1 (MLE: le mrel0 mrel1), sim_val mrel0 <2= sim_val mrel1;
    sim_val_list_spec: forall sm0, (List.Forall2 sm0.(sim_val) = sm0.(sim_val_list));
    sim_val_int: forall sm0 v_src v_tgt, sim_val sm0 v_src v_tgt -> forall i, v_src = Vint i -> v_tgt = Vint i;
  }.

  Lemma sim_val_list_length
        `{SM: class} (sm0: t)
        vs_src vs_tgt
        (SIMVS: sm0.(sim_val_list) vs_src vs_tgt):
      length vs_src = length vs_tgt.
  Proof. rewrite <- sim_val_list_spec in SIMVS. ginduction SIMVS; ii; ss. congruence. Qed.

  Definition sim_block `{SM: class} (sm0: t) (blk_src blk_tgt: block): Prop :=
    sm0.(sim_val) (Vptr blk_src Ptrofs.zero) (Vptr blk_tgt Ptrofs.zero).

  Definition future `{SM: class}: t -> t -> Prop := rtc (lepriv \2/ le).


  Definition sim_regset `{SM: class} (sm0: SimMem.t) (rs_src rs_tgt: Asm.regset): Prop := forall pr, sm0.(sim_val) (rs_src pr) (rs_tgt pr).

  Inductive sim_args `{SM: class} (args_src args_tgt: Args.t) (sm0: SimMem.t): Prop :=
  | sim_args_Cstyle
      fptr_src vs_src m_src fptr_tgt vs_tgt m_tgt
      (CSRC: args_src = Args.Cstyle fptr_src vs_src m_src)
      (CTGT: args_tgt = Args.Cstyle fptr_tgt vs_tgt m_tgt)
      (FPTR: sm0.(SimMem.sim_val) fptr_src fptr_tgt)
      (VALS: sm0.(SimMem.sim_val_list) vs_src vs_tgt)
      (MEMSRC: m_src = sm0.(SimMem.src))
      (MEMTGT: m_tgt = sm0.(SimMem.tgt))
  | sim_args_Asmstyle
      rs_src m_src rs_tgt m_tgt
      (ASMSRC: args_src = Args.Asmstyle rs_src m_src)
      (ASMTGT: args_tgt = Args.Asmstyle rs_tgt m_tgt)
      (RS: (sim_regset sm0) rs_src rs_tgt)
      (MEMSRC: m_src = sm0.(SimMem.src))
      (MEMTGT: m_tgt = sm0.(SimMem.tgt)).

  Inductive sim_retv `{SM: class} (retv_src retv_tgt: Retv.t) (sm0: SimMem.t): Prop :=
  | sim_retv_Cstyle
      v_src m_src v_tgt m_tgt
      (CSRC: retv_src = Retv.Cstyle v_src m_src)
      (CTGT: retv_tgt = Retv.Cstyle v_tgt m_tgt)
      (RETV: sm0.(SimMem.sim_val) v_src v_tgt)
      (MEMSRC: m_src = sm0.(SimMem.src))
      (MEMTGT: m_tgt = sm0.(SimMem.tgt))
  | sim_retv_Asmstyle
      rs_src m_src rs_tgt m_tgt
      (ASMSRC: retv_src = Retv.Asmstyle rs_src m_src)
      (ASMTGT: retv_tgt = Retv.Asmstyle rs_tgt m_tgt)
      (RS: (sim_regset sm0) rs_src rs_tgt)
      (MEMSRC: m_src = sm0.(SimMem.src))
      (MEMTGT: m_tgt = sm0.(SimMem.tgt)).

  Lemma sim_args_sim_fptr `{SM: class}: forall sm0 args_src args_tgt (ARGS: sim_args args_src args_tgt sm0),
      sm0.(sim_val) (Args.get_fptr args_src) (Args.get_fptr args_tgt).
  Proof. i. inv ARGS; ss. Qed.

  Lemma sim_val_list_le
        `{SM: class}
        sm0 sm1 vs_src vs_tgt
        (LEPRIV: SimMem.le sm0 sm1)
        (SIMVS: SimMem.sim_val_list sm0 vs_src vs_tgt):
      <<SIMVS: SimMem.sim_val_list sm1 vs_src vs_tgt>>.
  Proof.
    rewrite <- sim_val_list_spec in *. induction SIMVS; ii; ss.
    econs; eauto. eapply le_sim_val; et.
  Qed.

End SimMem.

Hint Unfold SimMem.future.

Hint Resolve SimMem.pub_priv.


Module SimMemOh.
Section SimMemOh.

  (* Context {SM: SimMem.class}. *)
  (* Variable owned_heap_src owned_heap_tgt: Type. *)

  Local Open Scope signature_scope.
  Class class {SM: SimMem.class} (owned_heap_src owned_heap_tgt: Type) :=
  {
    t: Type;
    sm:> t -> SimMem.t;
    oh_src: t -> owned_heap_src;
    oh_tgt: t -> owned_heap_tgt;
    wf: t -> Prop;
    le: t -> t -> Prop;
    lepriv: t -> t -> Prop;

    le_PreOrder :> PreOrder le;

    pub_priv: forall smo0 smo1, le smo0 smo1 -> lepriv smo0 smo1;

    wf_proj: wf <1= SimMem.wf <*> sm;
    le_proj: (le ==> SimMem.le) sm sm; (* TODO: better style? *)
    lepriv_proj: (lepriv ==> SimMem.lepriv) sm sm; (* TODO: better style? *)
  }.

  Coercion SimMemOh.sm: SimMemOh.t >-> SimMem.t.

  Definition sim_args `{SMO: class} (oh_src: owned_heap_src) (oh_tgt: owned_heap_tgt)
             (args_src args_tgt: Args.t) (smo0: SimMemOh.t): Prop :=
    (<<SIMARGS: SimMem.sim_args args_src args_tgt smo0>>) /\
    (<<OHSRC: oh_src = smo0.(SimMemOh.oh_src)>>) /\ (<<OHTGT: oh_tgt = smo0.(SimMemOh.oh_tgt)>>)
  .

  Definition sim_retv `{SMO: class} (oh_src: owned_heap_src) (oh_tgt: owned_heap_tgt)
             (retv_src retv_tgt: Retv.t) (smo0: SimMemOh.t): Prop :=
    (<<SIMARGS: SimMem.sim_retv retv_src retv_tgt smo0>>) /\
    (<<OHSRC: oh_src = smo0.(SimMemOh.oh_src)>>) /\ (<<OHTGT: oh_tgt = smo0.(SimMemOh.oh_tgt)>>)
  .

End SimMemOh.
End SimMemOh.
Coercion SimMemOh.sm: SimMemOh.t >-> SimMem.t.


Local Obligation Tactic := try (by econs); try (by ii; ss).

Global Program Instance SimMemOh_default (SM: SimMem.class): (SimMemOh.class unit unit) | 100 :=
  {
    sm := id;
    wf := SimMem.wf;
    le := SimMem.le;
    lepriv := SimMem.lepriv;
  }
.
Next Obligation. i. eapply SimMem.pub_priv; eauto. Qed.


(* Section TEST. *)

(*   Variable A B: Type. *)
(*   Context {SM: SimMem.class}. *)
(*   Context {SMO: SimMemOh.class A B}. *)

(*   Check SimMem.t. *)
(*   Check (SimMemOh.t). *)
(*   Set Printing All. *)
(*   Variable ab: (@SimMemOh.t SM A B SMO). *)
(*   Variable abc: (SimMemOh.t (SM := SM) (owned_heap_src := A) (owned_heap_tgt := B)). *)
(*   Variable abcd: SimMemOh.t. *)
(*   Fail Check abcd: SimMem.t. *)
(*   Check abcd.(SimMemOh.sm): SimMem.t. *)
(*   Print Coercions. *)
(*   Coercion SimMemOh.sm: SimMemOh.t >-> SimMem.t. *)
(*   Check abcd: SimMem.t. *)

(* End TEST. *)

Module SimMemOhs.
Section SimMemOhs.

  (* Context {SM: SimMem.class}. *)
  (* Variable owned_heap_src owned_heap_tgt: Type. *)

  Local Open Scope signature_scope.
  Class class {SM: SimMem.class} :=
  {
    t: Type;
    sm:> t -> SimMem.t;
    ohs_src: t -> Ohs;
    ohs_tgt: t -> Ohs;
    wf: t -> Prop;
    le: t -> t -> Prop;
    lepriv: t -> t -> Prop;

    le_PreOrder :> PreOrder le;

    pub_priv: forall smo0 smo1, le smo0 smo1 -> lepriv smo0 smo1;

    wf_proj: wf <1= SimMem.wf <*> sm;
    le_proj: (le ==> SimMem.le) sm sm; (* TODO: better style? *)
    lepriv_proj: (lepriv ==> SimMem.lepriv) sm sm; (* TODO: better style? *)
  }.

  Coercion SimMemOhs.sm: SimMemOhs.t >-> SimMem.t.

  Require Import Program.

  Definition sim_args `{SMOS: class} (midx: Midx.t) (ohs_src: Ohs) (ohs_tgt: Ohs)
             (args_src args_tgt: Args.t) (smo0: SimMemOhs.t): Prop :=
    (<<SIMARGS: SimMem.sim_args args_src args_tgt smo0>>) /\
    (* (<<OHSRC: ohs_src midx ~= projT2 (smo0.(SimMemOhs.ohs_src) midx)>>) /\ *)
    (* (<<OHTGT: ohs_tgt midx ~= projT2 (smo0.(SimMemOhs.ohs_tgt) midx)>>) *)

    (<<OHSRC: nth_error ohs_src midx = (nth_error smo0.(SimMemOhs.ohs_src) midx)>>) /\
    (<<OHTGT: nth_error ohs_tgt midx = (nth_error smo0.(SimMemOhs.ohs_tgt) midx)>>)

    (* (<<OHSRC: ohs_src = (smo0.(SimMemOhs.ohs_src))>>) /\ *)
    (* (<<OHTGT: ohs_tgt = (smo0.(SimMemOhs.ohs_tgt))>>) *)
  .

  Definition sim_retv `{SMOS: class} (midx: Midx.t) (ohs_src: Ohs) (ohs_tgt: Ohs)
             (retv_src retv_tgt: Retv.t) (smo0: SimMemOhs.t): Prop :=
    (<<SIMARGS: SimMem.sim_retv retv_src retv_tgt smo0>>) /\
    (* (<<OHSRC: ohs_src midx ~= projT2 (smo0.(SimMemOhs.ohs_src) midx)>>) /\ *)
    (* (<<OHTGT: ohs_tgt midx ~= projT2 (smo0.(SimMemOhs.ohs_tgt) midx)>>) *)

    (<<OHSRC: nth_error ohs_src midx = (nth_error smo0.(SimMemOhs.ohs_src) midx)>>) /\
    (<<OHTGT: nth_error ohs_tgt midx = (nth_error smo0.(SimMemOhs.ohs_tgt) midx)>>)

    (* (<<OHSRC: ohs_src = (smo0.(SimMemOhs.ohs_src))>>) /\ *)
    (* (<<OHTGT: ohs_tgt = (smo0.(SimMemOhs.ohs_tgt))>>) *)
  .

End SimMemOhs.
End SimMemOhs.
Coercion SimMemOhs.sm: SimMemOhs.t >-> SimMem.t.


