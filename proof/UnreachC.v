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

(* Require Import IntegersC LinkingC. *)
(* Require Import SimSymb Skeleton Mod ModSem. *)
Require Import ModSem Skeleton.
(* Require SimSymbId. *)
(* Require Import SimMem. *)

Require Import Sound.
Require Unreach.
(* Export Unreach. *)
(* Include Unreach. *)
Import Unreach.
Require Import SemiLattice.
Require Import FinFun.

Set Implicit Arguments.


Local Open Scope nat.

(* Coercion unreach: t >-> Funclass. *)
(* Coercion Unreach.nb: Unreach.t >-> block. *)
(* Identity Coercion block_to_pos: block >-> positive. *)







(* TODO: Move to CoqlibC.v *)
Lemma app_eq_inv
      A
      (x0 x1 y0 y1: list A)
      (EQ: x0 ++ x1 = y0 ++ y1)
      (LEN: x0.(length) = y0.(length))
  :
    x0 = y0 /\ x1 = y1
.
Proof.
  ginduction x0; ii; ss.
  { destruct y0; ss. }
  destruct y0; ss. clarify.
  exploit IHx0; eauto. i; des. clarify.
Qed.

(* TODO: move to ??? *)
Lemma pos_elim_succ
      p
  :
    <<ONE: p = 1%positive>> \/
    <<SUCC: exists q, q.(Pos.succ) = p>>
.
Proof.
  hexploit (Pos.succ_pred_or p); eauto. i; des; ss; eauto.
Qed.

Lemma ple_elim_succ
      p q
      (PLE: Ple p q)
  :
    <<EQ: p = q>> \/
    <<SUCC: Ple p.(Pos.succ) q>>
.
Proof.
  revert_until p.
  pattern p. apply Pos.peano_ind; clear p; i.
  { hexploit (pos_elim_succ q); eauto. i. des; clarify; eauto.
    right. r. xomega. }
  hexploit (pos_elim_succ q); eauto. i.
  des; clarify.
  { left. xomega. }
  exploit H; eauto.
  { it q0. xomega. }
  i; des; clarify.
  - left. r. xomega.
  - right. r. xomega.
Qed.








Definition val' (su: Unreach.t) (v: val): Prop :=
  forall blk ofs (PTR: v = Vptr blk ofs true), ~su blk /\ (blk < su.(nb))%positive
.

Definition memval' (su: Unreach.t) (mv: memval): Prop :=
  forall v q n (PTR: mv = Fragment v q n), su.(val') v
.

Inductive mem': Unreach.t -> Memory.mem -> Prop :=
| mem'_intro
    (su: Unreach.t) m0
    (SOUND: forall
        blk ofs
        (PUB: ~ su blk)
        (PERM: Mem.perm m0 blk ofs Cur Readable) (* <------------ Cur? *)
      ,
        su.(memval') (ZMap.get ofs (Mem.mem_contents m0) !! blk))
    (BOUND: su.(Unreach.unreach) <1= m0.(Mem.valid_block))
    (* (BOUND: Ple su.(Unreach.nb) m0.(Mem.nextblock)) *)
    (GENB: Ple su.(Unreach.ge_nb) m0.(Mem.nextblock))
    (NB: su.(Unreach.nb) = m0.(Mem.nextblock))
  :
    mem' su m0
.

Lemma mle_mem
      su0 m0 m1
      (MEM: mem' su0 m0)
      (MLE: mle su0 m0 m1)
      (NB: Ple m0.(Mem.nextblock) m1.(Mem.nextblock))
  :
    <<MEM: mem' su0 m1>>
.
Proof.
  inv MEM.
  inv MLE.
  econs; eauto; cycle 1.
  { ii. unfold Mem.valid_block in *. exploit BOUND; eauto. i. xomega. }
  { xomega. }
  ii. clarify.
  (* MLE: private is not changed *)
  (* we need to show: public may changed, but still not pointing private *)
Abort.

Hint Unfold val' memval'.

Definition le' (x y: Unreach.t): Prop :=
  (<<PRIV: x.(unreach) <1= y.(unreach)>>)
  /\
  (<<PUB: x.(ge_nb) = y.(ge_nb)>>)
  (* /\ *)
  (* (<<NB: x.(nb) = y.(nb)>>) *)
.

Global Program Instance le'_PreOrder: PreOrder le'.
Next Obligation.
  ii; r; esplits; ss; eauto.
Qed.
Next Obligation.
  ii. r in H. r in H0. des.
  r; esplits; ss; eauto; etrans; eauto.
Qed.

(* TODO: I really don't want to define this. It is redundant with `Sound.args`, but it seems there is no other way *)
Definition args' (su: Unreach.t) (args0: Args.t) :=
  (<<VAL: val' su (Args.fptr args0)>>)
  /\ (<<VALS: List.Forall (su.(val')) (Args.vs args0)>>)
  /\ (<<MEM: mem' su (Args.m args0)>>)
  (* /\ (<<WF: forall blk (PRIV: su blk) (PUB: Plt blk su.(ge_nb)), False>>) *)
  (* /\ (<<WF: forall blk (PRIV: su blk) (PUB: Ple su.(nb) blk), False>>) *)
  /\ (<<WF: wf su>>)
.

Definition retv' (su: Unreach.t) (retv0: Retv.t) :=
  (<<VAL: val' su (Retv.v retv0)>>)
  /\ (<<MEM: mem' su (Retv.m retv0)>>)
  /\ (<<WF: forall blk (PRIV: su blk) (PUB: Ple su.(nb) blk), False>>)
.

Lemma finite_map
      X (P: X -> Prop) Y
      (j: X -> Y)
      (INJ: Injective j)
      (FIN: exists ly, forall x, P x -> In (j x) ly)
  :
    <<FIN: exists lx, forall x, P x -> In x lx>>
.
Proof.
  rr in FIN. des.
  ginduction ly; ii; ss.
  { exists []. ii. exploit FIN; eauto. }
  rename a into y0.
  specialize (IHly X (fun x => P x /\ j x <> y0) j INJ).
  exploit IHly; eauto.
  { ii. des. exploit FIN; eauto. i; des; ss; clarify. }
  i; des.
  destruct (classic (exists x0, j x0 = y0)); cycle 1.
  { eapply not_ex_all_not in H0. exists lx. i. eapply H. esplits; eauto. }
  des.
  exists (x0 :: lx).
  i. ss.
  destruct (classic (x0 = x)); eauto.
  right. eapply H; eauto. esplits; eauto. ii.
  assert(x0 = x).
  { eapply INJ. congruence. }
  clarify.
Qed.

Lemma finite_map_prop
      X (P: X -> Prop) Y
      (j: X -> Y -> Prop)
      (INJ: forall x0 x1 y, P x0 -> P x1 -> j x0 y -> j x1 y -> x0 = x1)
      (FUNC: forall x, P x -> exists y, j x y)
      (* (FUNC: forall x, exists ! y, j x y) *)
      (FIN: exists ly, forall x y, P x -> j x y -> In y ly)
  :
    <<FIN: exists lx, forall x, P x -> In x lx>>
.
Proof.
  rr in FIN. des.
  ginduction ly; ii; ss.
  { exists []. ii. exploit FUNC; eauto. i; des. (* destruct H0. destruct H0. *) exploit FIN; eauto. }
  rename a into y0.
  specialize (IHly X (fun x => P x /\ ~(j x y0)) j).
  exploit IHly; eauto.
  { ii. des. eauto. }
  { ii. des. eauto. }
  { ii. des. exploit FIN; eauto. i; des; ss; clarify. }
  i; des.
  destruct (classic (exists x0, j x0 y0 /\ P x0)); cycle 1.
  { eapply not_ex_all_not in H0. exists lx. i. eapply H. esplits; eauto. ii. eapply H0; eauto. }
  des.
  exists (x0 :: lx).
  i. ss.
  destruct (classic (x0 = x)); eauto.
  right. eapply H; eauto.
Qed.

Fixpoint range (n: nat): list nat :=
  match n with
  | 0%nat => [0]
  | S n => (S n) :: range n
  end
.

Lemma range_0
      bound
  :
    In 0 (range bound)
.
Proof.
  ginduction bound; ii; ss; try tauto.
Qed.

Lemma range_spec
      x bound
      (BDD: (x <= bound))
  :
    In x (range bound)
.
Proof.
  admit "ez".
Qed.

Lemma finite_nat
      X (P: X -> Prop)
      (j: positive -> X -> option nat)
      (fuel: positive)
      (INJ: Injective (j fuel))
      (FIN: exists bound, forall x, P x -> exists n, j fuel x = Some n /\ (n <= bound))
  :
    <<FIN: exists lx, forall x, P x -> In x lx>>
.
Proof.
  eapply finite_map with (j := j fuel); eauto. des.
  exists (map Some (range bound)). ii. exploit FIN; eauto. i.
  des; ss. rewrite H0.
  rewrite in_map_iff. esplits; eauto. eapply range_spec; eauto.
Qed.

Lemma finite_nat_prop
      X (P: X -> Prop)
      (j: positive -> X -> nat -> Prop)
      (fuel: positive)
      (INJ: forall x0 x1 n, P x0 -> P x1 -> j fuel x0 n -> j fuel x1 n -> x0 = x1)
      (FUNC: forall x, P x -> exists y, j fuel x y)
      (* (FIN: exists bound, forall x, P x -> exists n, j fuel x n /\ (n <= bound)) *)
      (FIN: exists bound, forall x n, P x -> j fuel x n -> (n <= bound))
  :
    <<FIN: exists lx, forall x, P x -> In x lx>>
.
Proof.
  eapply finite_map_prop with (j := j fuel); eauto.
  des.
  exists (range bound). ii. exploit FIN; eauto. i.
  eapply range_spec; eauto.
Qed.

Inductive J: positive -> Unreach.t -> nat -> Prop :=
| J_runout
    su 
  :
    J (1%positive) su 0
| J_true
    fuel su n
    (PRED: J fuel su n)
    (TRUE: su fuel = true)
  :
    J fuel.(Pos.succ) su (2 * n + 1)
| J_false
    fuel su n
    (PRED: J fuel su n)
    (FALSE: su fuel = false)
  :
    J fuel.(Pos.succ) su (2 * n)
.

Let eta
      x0 x1
      (FIELD0: x0.(unreach) = x1.(unreach))
      (FIELD1: x0.(ge_nb) = x1.(ge_nb))
      (FIELD2: x0.(nb) = x1.(nb))
  :
    <<EQ: x0 = x1>>
.
Proof. destruct x0, x1; ss. clarify. Qed.

Let J_injective: forall
    fuel x0 x1 n
    (J0: J fuel x0 n)
    (J1: J fuel x1 n)
    (BDD: forall blk, Ple fuel blk -> x0 blk = x1 blk)
    (GENB: x0.(ge_nb) = x1.(ge_nb))
    (NB: x0.(nb) = x1.(nb))
  ,
    x0 = x1
.
Proof.
  i.
  eapply eta; ss.
  apply func_ext1.
  revert_until fuel.
  pattern fuel.
  eapply Pos.peano_ind; clear fuel; i.
  - eapply BDD; eauto. xomega.
  - inv J0; inv J1; ss; try xomega.
    + assert(p = fuel) by (eapply Pos.succ_inj; eauto).
      assert(p = fuel0) by (eapply Pos.succ_inj; eauto).
      clarify. clear_tac.
      assert(n = n0) by xomega. clarify.
      exploit H; [exact PRED|exact PRED0|..]; eauto.
      { i. eapply ple_elim_succ in H0. des; clarify.
        eapply BDD; eauto.
      }
    + assert(p = fuel) by (eapply Pos.succ_inj; eauto).
      assert(p = fuel0) by (eapply Pos.succ_inj; eauto).
      clarify. clear_tac.
      assert(n = n0) by xomega. clarify.
      exploit H; [exact PRED|exact PRED0|..]; eauto.
      { i. eapply ple_elim_succ in H0. des; clarify.
        eapply BDD; eauto.
      }
Qed.

Let J_func: forall
    fuel x
  ,
    exists n, J fuel x n
.
Proof.
  intro fuel. pattern fuel.
  eapply Pos.peano_ind; clear fuel; i.
  - esplits; eauto. econs; eauto.
  - specialize (H x). des.
    destruct (x p) eqn:T.
    + esplits; eauto.
      econs; eauto.
    + esplits; eauto.
      econsr; eauto.
Qed.

Let J_bound: forall
    fuel x n
    (J: J fuel x n)
  ,
    (n <= 3 ^ fuel.(Pos.to_nat))%nat
.
Proof.
  intro fuel. pattern fuel.
  eapply Pos.peano_ind; clear fuel; i.
  { inv J0; try xomega. }
  generalize (Pos2Nat.is_pos p); intro POS.
  inv J0; try xomega; exploit Pos.succ_inj; eauto; i; clarify; clear_tac; hexploit H; eauto; i.
  - ss. rewrite Pos2Nat.inj_succ. ss.
    rewrite ! Nat.add_0_r. rewrite Nat.add_assoc.
    destruct (classic (n0 = 0)).
    { clarify. ss. assert(1 <= Pos.to_nat p) by xomega.
      assert(1 < 3 ^ Pos.to_nat p).
      { eapply Nat.pow_gt_1; eauto. xomega. }
      xomega.
    }
    xomega.
  - ss. rewrite Pos2Nat.inj_succ. ss.
    rewrite ! Nat.add_0_r. rewrite Nat.add_assoc.
    destruct (classic (n0 = 0)).
    { clarify. ss. xomega. }
    xomega.
Unshelve.
  all: ss.
Qed.

Let to_inj (su: t) (bound: positive): meminj :=
  fun blk =>
    if (su blk)
    then None
    else
      (if plt blk bound
       then Some (blk, 0%Z)
       else None)
.

Let to_su (j: meminj) (ge_nb: block) (bound: positive): t :=
  mk
    (fun blk =>
       if plt blk bound
       then
         match j blk with
         | Some _ => false
         | None => true
         end
       else
         false)
    ge_nb
    bound
.

Let to_inj_mem: forall
    su m
    (SUM: mem' su m)
  ,
    @Mem.inject Val.mi_normal (to_inj su m.(Mem.nextblock)) m m
.
Proof.
  i. unfold to_inj. inv SUM. u in BOUND.
  econs; eauto; ii; ss; des_ifs; zsimpl; ss; try tauto.
  - econs; ii; ss; des_ifs; zsimpl; eauto.
    + apply Z.divide_0_r.
    + spc SOUND. spc SOUND.
      hexploit SOUND; eauto.
      { ii. bsimpl. clarify. }
      intro MV; des.
      r in MV.
      abstr (ZMap.get ofs (Mem.mem_contents m) !! b2) mv.
      destruct mv; ss; try (by econs; eauto).
      destruct v; ss; try (by econs; eauto).
      destruct b0; ss; try (by econs; eauto).
      destruct (su b) eqn:T.
      { exploit MV; ss; eauto. i; des. ss. }
      econs; eauto. econs; eauto.
      { des_ifs. exploit MV; eauto. i; des. rewrite NB in *. ss. }
      rewrite Ptrofs.add_zero. ss.
  - split.
    + eauto with xomega.
    + eapply Ptrofs.unsigned_range_2; eauto.
Qed.

Definition lub (x y: t): option t :=
  if eq_block x.(ge_nb) y.(ge_nb) then
    if eq_block x.(nb) y.(nb)
    then Some (mk (fun blk => orb (x blk) (y blk)) x.(ge_nb) x.(nb))
    else None
  else None
.
Hint Unfold lub.

Lemma lubsucc: forall
    su0 x y args
    (PX: le' su0 x /\ args' x args)
    (PY: le' su0 y /\ args' y args)
  ,
    exists z, <<LUB: lub x y = Some z>>
.
Proof.
  ii. des. unfold le', args' in *. des.
  u. des_ifs; try congruence.
  - econs; ii; eauto.
  - inv MEM. inv MEM0. congruence.
Qed.

Lemma lubspec: forall
    x y z
    (LUB: lub x y = Some z)
  ,
    (<<LE: le' x z>>) /\ (<<LE: le' y z>>)
.
Proof.
  ii. unfold lub in *. des_ifs. unfold le'.
  esplits; ii; ss; bsimpl; ss; eauto.
Qed.

Lemma lubclosed: forall
    su0 args x y
    (PX: <<LE: le' su0 x>> /\ args' x args)
    (PY: <<LE: le' su0 y>> /\ args' y args)
    z
    (LUB: lub x y = Some z)
  ,
    <<PXY: le' su0 z /\ args' z args>>
.
Proof.
  ii. des. unfold lub in *. des_ifs. inv PX0. inv PY0. des. u in *.
  rewrite Forall_forall in *.
  esplits; eauto.
  { clear - LE LE0. r in LE. r in LE0. u in *. r. ii; ss. bsimpl. des. esplits; ii; ss.
    repeat spc LE. repeat spc LE0. bsimpl. eauto. }
  r; esplits; u; ii; bsimpl; ss; des; eauto.
  { repeat (spc H). repeat (spc H1). des. esplits; eauto. ii; des; eauto. }
  { rewrite Forall_forall in *. i. repeat (spc VALS0). repeat (spc VALS). des. esplits; eauto. ii; bsimpl; ss; des; eauto. }
  { inv MEM0. inv MEM.
    econs; ss.
    + ii; clarify. bsimpl. Nsimpl. des_safe; eauto.
      unfold memval', val' in *.
      hexpl SOUND; hexpl SOUND0; eauto.
      esplits; eauto. ii. ss. bsimpl. des; eauto.
    + ii. bsimpl. des; eauto.
  }
  { inv WF0. inv WF.
    rewrite <- e in *. rewrite <- e0 in *.
    econs; ss; i; eauto.
    - bsimpl. des; eauto with congruence.
    - bsimpl. des; eauto with congruence.
  }
Qed.

(* copied from Globalenvs.v - store_init_data *)
Definition loadable_init_data (m: mem) (ske: SkEnv.t) (b: block) (p: Z) (id: init_data): Prop :=
  match id with
  | Init_int8 n => Mem.load Mint8unsigned m b p = Some (Vint n)
  | Init_int16 n => Mem.load Mint16unsigned m b p = Some (Vint n)
  | Init_int32 n => Mem.load Mint32 m b p = Some (Vint n)
  | Init_int64 n => Mem.load Mint64 m b p = Some (Vlong n)
  | Init_float32 n => Mem.load Mfloat32 m b p = Some (Vsingle n)
  | Init_float64 n => Mem.load Mfloat64 m b p = Some (Vfloat n)
  | Init_addrof symb ofs =>
      match ske.(Genv.find_symbol) symb with
      | None => False
      | Some b' => Mem.load Mptr m b p = Some (Vptr b' ofs true)
      end
  | Init_space n => True
  end
.

Fixpoint loadable_init_data_list (m: mem) (ske: SkEnv.t) (b: block) (p: Z) (idl: list init_data): Prop :=
  match idl with
  | nil => True
  | id :: idl' => <<HD: loadable_init_data m ske b p id>> /\ <<TL: loadable_init_data_list m ske b (p + init_data_size id) idl'>>
  end.

(* copied from ValueAnalysis.v *)
Definition definitive_initializer (init: list init_data) : bool :=
  match init with
  | nil => false
  | Init_space _ :: nil => false
  | _ => true
  end.

Require Import ValueAnalysis ValueDomain.


Definition romatch_ske (bc: block_classification) (m: mem) (rm: ident -> option ablock): Prop :=
  forall
    b id ab
    (BC: bc b = BCglob id)
    (RO: rm id = Some ab)
  ,
    pge Glob (ab_summary ab) /\ bmatch bc m b ab /\ (forall ofs : Z, ~ Mem.perm m b ofs Max Writable)
.

Lemma romatch_ske_unchanged_on
      (ske: SkEnv.t) m0 m1 rm
      (RO: Mem.unchanged_on (loc_not_writable m0) m0 m1)
      (NB: Ple (Genv.genv_next ske) (Mem.nextblock m0))
      (ROMATCH: romatch_ske (ske2bc ske) m0 rm)
  :
    <<ROMATCH: romatch_ske (ske2bc ske) m1 rm>>
.
Proof.
  ii. exploit ROMATCH; et. i; des.
  assert(VAL: Mem.valid_block m0 b).
  { ss. des_ifs. clear - NB Heq. admit "NB". }
  esplits; et.
  - eapply bmatch_ext; et. i.
    erewrite <- Mem.loadbytes_unchanged_on_1; et.
    ii. eapply H1; et.
  - ii. eapply H1; et. eapply Mem.perm_unchanged_on_2; et.
    { ii. eapply H1; et. }
Qed.

Definition romem_for_ske (ske: SkEnv.t): ident -> option ablock :=
  fun id =>
    match ske.(Genv.find_symbol) id with
    | Some blk =>
      match ske.(Genv.find_var_info) blk with
      | Some gv =>
        (* if <<RO: gv.(gvar_readonly)>> && <<NONVOL: negb gv.(gvar_volatile)>> *)
        (*        && <<DEFI: definitive_initializer gv.(gvar_init)>> *)
        if gv.(gvar_readonly) && negb gv.(gvar_volatile)
               && definitive_initializer gv.(gvar_init)
        then Some (store_init_data_list (ablock_init Pbot) 0 (gvar_init gv))
        else None
      | None => None
      end
    | None => None
    end
.

Lemma romem_for_ske_complete
      blk ske id gv
      (SYMB: ske.(Genv.find_symbol) id = Some blk)
      (VAR: ske.(Genv.find_var_info) blk = Some gv)
      (RO: gv.(gvar_readonly) = true)
      (VOL: gv.(gvar_volatile) = false)
      (DEFI: definitive_initializer gv.(gvar_init) = true)
  :
    (romem_for_ske ske) id = Some (store_init_data_list (ablock_init Pbot) 0 (gvar_init gv))
.
Proof.
  unfold romem_for_ske. des_ifs.
Qed.

(* Lemma romem_for_ske_romem_for *)
(*       sk *)
(*   : *)
(*     romem_for_ske sk.(Genv.globalenv) = romem_for sk *)
(* . *)
(* Proof. *)
(*   admit "". *)
(* Qed. *)

Section ROMEM_COMPLETE.

Variable F: Type.

Definition romem_complete (defmap: PTree.t (globdef F unit)) (rm: romem): Prop :=
  forall
    id gv
    (DEFMAP: defmap!id = Some (Gvar gv))
    (RO: gv.(gvar_readonly) = true)
    (VOL: gv.(gvar_volatile) = false)
    (DEFI: definitive_initializer gv.(gvar_init) = true)
  ,
    rm!id = Some (store_init_data_list (ablock_init Pbot) 0 gv.(gvar_init))
.

Lemma alloc_global_complete:
  forall dm rm idg,
  romem_complete dm rm ->
  romem_complete (PTree.set (fst idg) (snd idg) dm) (alloc_global rm idg).
Proof.
  intros; red; intros. destruct idg as [id1 [f1 | v1]]; simpl in *.
- rewrite PTree.grspec. destruct (PTree.elt_eq id id1); try discriminate.
  { clarify. rewrite PTree.gsspec in *. des_ifs. }
  rewrite PTree.gso in DEFMAP by auto. apply H; auto.
- destruct (gvar_readonly v1 && negb (gvar_volatile v1) && definitive_initializer (gvar_init v1)) eqn:T.
+ InvBooleans. rewrite negb_true_iff in H3.
  rewrite PTree.gsspec in *. des_ifs.
* apply H; auto.
+ rewrite PTree.grspec. rewrite PTree.gsspec in *. des_ifs. apply H; auto.
Qed.

Lemma romem_for_complete:
  forall cunit, romem_complete (prog_defmap cunit) (romem_for cunit).
Proof.
  assert (REC: forall l dm rm,
            romem_complete dm rm ->
            romem_complete (fold_left (fun m idg => PTree.set (fst idg) (snd idg) m) l dm)
                           (fold_left alloc_global l rm)).
  { induction l; intros; simpl; auto. apply IHl. apply alloc_global_complete; auto. }
  intros. apply REC.
  red; intros. rewrite PTree.gempty in *; discriminate.
Qed.

End ROMEM_COMPLETE.

Lemma romatch_romatch_ske
      m_init sk_link
      (RO : romatch (ske2bc (Genv.globalenv sk_link)) m_init (romem_for sk_link))
  :
    <<RO: romatch_ske (ske2bc (Genv.globalenv sk_link)) m_init (romem_for_ske (Genv.globalenv sk_link))>>
.
Proof.
  ii. eapply RO; et. clear RO.
  ss. des_ifs. unfold romem_for_ske in *. des_ifs. bsimpl. des.
  exploit Genv.invert_find_symbol; et. i; des. clarify.
  hexploit (romem_for_complete sk_link); eauto. intro CO.
  eapply CO; ss.
  eapply Genv.find_def_symbol; et. esplits; et. uge. des_ifs.
Qed.

Inductive skenv (su: Unreach.t) (m0: mem) (ske: SkEnv.t): Prop :=
| skenv_intro
    (PUB: su.(ge_nb) = ske.(Genv.genv_next))
    (* (BMATCH: forall *)
    (*     id blk gv *)
    (*     (SYMB: ske.(Genv.find_symbol) id = Some blk) *)
    (*     (GVAR: ske.(Genv.find_var_info) blk = Some gv) *)
    (*     (GRO: gv.(gvar_readonly)) *)
    (*     (GVOL: ~ gv.(gvar_volatile)) *)
    (*     (GDEF: definitive_initializer gv.(gvar_init)) *)

    (*     ske_proj (sk_proj: Sk.t) *)
    (*     (PROJ: SkEnv.project_spec ske sk_proj.(defs) ske_proj) *)
    (*     bc *)
    (*     (GMATCH: genv_match bc ske_proj) *)
    (*   , *)
    (*     <<BMATCH: bmatch bc m0 blk (store_init_data_list (ablock_init Pbot) 0 gv.(gvar_init))>>) *)
    (* (BMATCH: *)
    (*     <<GMATCH: genv_match ske.(ske2bc) ske>> *)
    (*     /\ *)
    (*     <<ROMATCH: romatch ske.(ske2bc) m0 (romem_for_ske ske)>> *)
    (*     (* <<BMATCH: bmatch bc m0 blk (store_init_data_list (ablock_init Pbot) 0 gv.(gvar_init))>> *) *)
    (* ) *)
    (ROMATCH: romatch_ske ske.(ske2bc) m0 (romem_for_ske ske))
    (* (RO: forall *)
    (*     blk gv *)
    (*     (GVAR: ske.(Genv.find_var_info) blk = Some gv) *)
    (*     (* copied from ValueAnalysis - alloc_global *) *)
    (*     (GRO: gv.(gvar_readonly)) *)
    (*     (GVOL: ~ gv.(gvar_volatile)) *)
    (*     (GDEF: definitive_initializer gv.(gvar_init)) *)
    (*   , *)
    (*     (* <<LABLE: loadable_init_data_list m0 ske blk 0 gv.(gvar_init)>> *) *)
    (*     (<<PERM: forall *)
    (*         ofs p *)
    (*         (PERM: Mem.perm m0 blk ofs Max p) *)
    (*       , *)
    (*         <<OFS: (0 <= ofs < init_data_list_size gv.(gvar_init))%Z>> /\ <<ORD: perm_order Readable p>>>>) /\ *)
    (*     (<<LABLE: Genv.load_store_init_data ske m0 blk 0 gv.(gvar_init)>>)) *)
    (NB: Ple ske.(Genv.genv_next) m0.(Mem.nextblock))
.

(* Lemma loadbytes_loadable *)
(*       sk_link m0 blk ids lo *)
(*       (LO: (0 <= lo)%Z) *)
(*       (GDEF: definitive_initializer ids) *)
(*       (LOAD: Mem.loadbytes m0 blk lo (init_data_list_size ids) = *)
(*              Some (Genv.bytes_of_init_data_list (Genv.globalenv sk_link) ids)) *)
(*   : *)
(*     <<LOADABLE: loadable_init_data_list m0 (Genv.globalenv sk_link) blk lo ids>> *)
(* . *)
(* Proof. *)
(*   ginduction ids; ii; ss. *)
(*   eapply Mem.loadbytes_split in LOAD; cycle 1. *)
(*   { eapply init_data_size_pos. } *)
(*   { eapply init_data_list_size_pos. } *)
(*   des. ss. *)
(*   eapply app_eq_inv in LOAD1; cycle 1. *)
(*   { set (X := a). *)
(*     destruct a; ss; *)
(*       repeat (rewrite length_inj_bytes; ss; check_safe); *)
(*       repeat (rewrite encode_int_length; ss; check_safe); *)
(*       repeat (rewrite length_list_repeat; ss; check_safe); *)
(*       repeat (erewrite Mem.loadbytes_length; eauto; ss; check_safe). *)
(*     - des_ifs. *)
(*     { instantiate (1:= (init_data_size a)). *)
(*       ss. } *)
(*   exploit IHids; eauto. *)
(* Qed. *)

(* Lemma hle_le *)
(*       su0 su1 *)
(*       (HLE: hle su0 su1) *)
(*   : *)
(*     <<LE: le' su0 su1>> *)
(* . *)
(* Proof. *)
(*   rr. rr in HLE. des. esplits; eauto. *)
(* Qed. *)


Definition bc_proj (bc1 bc2: block_classification) : Prop :=
  forall b, bc1 b = bc2 b \/ exists id, bc1 b = BCglob id /\ bc2 b = BCother
.

Section MATCH_PROJ.

Variables bc1 bc2: block_classification.
Hypothesis PROJ: bc_proj bc1 bc2.

Lemma pmatch_proj: forall b ofs isreal p (GOOD: exists id, bc2 b = BCglob id), pmatch bc1 b ofs isreal p -> pmatch bc2 b ofs isreal p.
Proof.
  i. hexploit (PROJ b); eauto. i. des; try congruence.
  inv H; try (by econs; eauto; congruence).
Qed.

Lemma vmatch_proj: forall v x (GOOD: forall blk ofs (PTR: v = Vptr blk ofs true), exists id, bc2 blk = BCglob id), vmatch bc1 v x -> vmatch bc2 v x.
Proof.
  i. inv H; econs; eauto.
  - destruct isreal; ss.
    + exploit GOOD; eauto. i. des. eapply pmatch_proj; eauto.
    + inv H0; econs; eauto.
  - destruct isreal; ss.
    + exploit GOOD; eauto. i. des. eapply pmatch_proj; eauto.
    + inv H0; econs; eauto.
Qed.

Lemma smatch_proj: forall m b p (GOOD: exists id, bc2 b = BCglob id)
                          (GOODMEM: forall chunk ofs_ v
                                           (LOAD: Mem.load chunk m b ofs_ = Some v)
                                           blk ofs
                                           (PTR: v = Vptr blk ofs true)
                            , exists id, bc2 blk = BCglob id)
                          (GOODMEMVAL: forall lo_ hi_ mv
                                           (LOAD: Mem.loadbytes m b lo_ hi_ = Some mv)
                                           blk ofs q n
                                           (PTR: mv = [Fragment (Vptr blk ofs true) q n])
                            , exists id, bc2 blk = BCglob id)
  , smatch bc1 m b p -> smatch bc2 m b p.
Proof.
  intros. destruct H as [A B]. split; intros.
  apply vmatch_proj; eauto.
  destruct isreal'; cycle 1.
  { exploit B; eauto. i. inv H0; econs; eauto. }
  apply pmatch_proj; eauto.
Qed.

Lemma bmatch_proj: forall m b ab (GOOD: exists id, bc2 b = BCglob id)
                          (GOODMEM: forall chunk ofs_ v
                                           (LOAD: Mem.load chunk m b ofs_ = Some v)
                                           blk ofs
                                           (PTR: v = Vptr blk ofs true)
                            , exists id, bc2 blk = BCglob id)
                          (GOODMEMVAL: forall lo_ hi_ mv
                                           (LOAD: Mem.loadbytes m b lo_ hi_ = Some mv)
                                           blk ofs q n
                                           (PTR: mv = [Fragment (Vptr blk ofs true) q n])
                            , exists id, bc2 blk = BCglob id)
  , bmatch bc1 m b ab -> bmatch bc2 m b ab.
Proof.
  intros. destruct H as [B1 B2]. split.
  apply smatch_proj; auto.
  intros. apply vmatch_proj; eauto.
Qed.

End MATCH_PROJ.

Global Program Instance Unreach: Sound.class := {
  t := Unreach.t;
  le := le';
  wf := wf;
  hle := hle;
  val := val';
  mem := mem';
  get_greatest (su0: t) (args: Args.t) := greatest le' (fun su => <<LE: le' su0 su>> /\ su.(args') args);
  (* mle := Unreach.mle; *) (* TODO: How did `Program` guess the implementation of `mle` ???? *)
  skenv := skenv;
}
.
Next Obligation.
  rr. rr in HLE. des. esplits; eauto.
  ii. rewrite <- OLD; ss. inv WF. eauto.
Qed.
Next Obligation.
  eapply mle_monotone; try apply MLE; eauto.
  r in LE. des; ss.
Qed.
Next Obligation.
  rr in HLE. des. rr in VAL. rr.
  ii. clarify. exploit VAL; eauto. i; des.
  esplits; eauto.
  - rewrite <- OLD; ss.
  - xomega.
Qed.
Next Obligation.
  rr in GR0. rr in GR1. des.
  assert(le' su_gr0 su_gr1).
  { eauto. }
  assert(le' su_gr1 su_gr0).
  { eauto. }
  rr in H. rr in H0. des.
  eapply eta; ss.
  apply func_ext1; i.
  destruct (su_gr0 x0) eqn:T0, (su_gr1 x0) eqn:T1; ss.
  { rewrite PRIV0 in *; eauto. }
  { rewrite PRIV in *; eauto. }
  { inv PROP0. inv PROP1. des. inv MEM0. inv MEM. congruence. }
Qed.
(* Next Obligation. *)
(*   rr in GR. des. eapply MAX; eauto. (* econs; eauto. *) *)
(* Qed. *)
Next Obligation.
  rename INHAB into inhab. rename H into INHAB. rename H0 into INHAB0.
  eapply find_greatest with (lub:= lub); eauto.
  - typeclasses eauto.
  - ii. eapply lubsucc; eauto.
  - ii. eapply lubspec; eauto.
  - rr. destruct args0.
    eapply finite_nat_prop with (j:= J) (fuel := m.(Mem.nextblock)); eauto.
    + ii. des. inv H0. inv H3. des; ss.
      inv MEM0. inv MEM1.
      eapply J_injective; eauto; cycle 1.
      { unfold le' in *. des. congruence. }
      { congruence. }
      ii. u in BOUND. u in BOUND0. destruct (x0 blk) eqn:T0, (x1 blk) eqn:T1; ss.
      { hexploit BOUND0; eauto. i. r in H4. xomega. }
      { hexploit BOUND; eauto. i. r in H4. xomega. }
    + ii. eapply J_func.
    + i. exists (3 ^ (m.(Mem.nextblock)).(Pos.to_nat))%nat. i.
      eapply J_bound; eauto.
  - ii. eapply lubclosed; try apply LUB; eauto.
Qed.
Next Obligation.
  rr in GR. des. eauto.
Qed.
Next Obligation.
  hexploit (@greatest_le_irr _ le' lub (fun su => args' su args0)); eauto.
  { typeclasses eauto. }
  { i. eapply lubsucc; eauto. }
  { i. eapply lubspec; eauto. }
  { i. eapply lubclosed; revgoals; eauto. }
  { rr. ss. }
Qed.
Next Obligation.
  set (Sk.load_skenv sk_link) as skenv.
  exists (mk (fun _ => false) skenv.(Genv.genv_next) m_init.(Mem.nextblock)).
  esplits; eauto.
  - rr; ss. esplits; eauto.
    + ii. esplits; eauto. unfold Genv.symbol_address in *. des_ifs. u in MEM. erewrite <- Genv.init_mem_genv_next; eauto.
      eapply Genv.genv_symb_range; eauto.
  - econs; eauto.
    + ii; ss. clarify. esplits; eauto.
      admit "this should hold - use Genv.initmem_inject".
    + ii; ss.
    + ss. u in *. erewrite <- Genv.init_mem_genv_next; eauto. folder. refl.
  - econs; eauto; ss.
  - econs; eauto; cycle 1.
    { subst skenv. u in *. erewrite Genv.init_mem_genv_next; eauto. refl. }
    + u in MEM. u in skenv.

      unfold Genv.init_mem in *. subst skenv.
      hexploit (initial_mem_matches _ _ MEM); eauto. intro IM; des. clarify.
      hexploit IM2; eauto.
      { apply Linking.linkorder_refl. }
      intro RO. eapply romatch_romatch_ske; et.
    (* + ii. u in *. subst skenv. *)
    (*   hexploit Genv.init_mem_characterization; eauto. intro CHAR. des. *)
    (*   hexploit Genv.init_mem_characterization_gen; eauto. intro X. r in X. *)
    (*   unfold Genv.find_var_info in *. des_ifs. *)
    (*   exploit (X blk (Gvar gv)); eauto. intro GEN; des. *)
    (*   unfold Genv.perm_globvar in *. des_ifs. *)
    (*   esplits; eauto. *)
Qed.
Next Obligation.
  inv LE.
  inv SKE. econs; eauto.
  congruence.
Qed.
Next Obligation.
  inv MLE.
  inv SKE. econs; eauto; cycle 1.
  { etrans; eauto. eauto with mem. }
  eapply romatch_ske_unchanged_on; et.
  (* - ii. exploit RO0; eauto. i; des. *)
  (*   esplits; eauto. *)
  (*   + ii. eapply PERM0; eauto. eapply PERM; eauto. *)
  (*     { r. eapply Plt_Ple_trans; eauto. *)
  (*       admit "ez - GVAR/genv_defs_range". *)
  (*     } *)
  (*   + eapply Genv.load_store_init_data_invariant; try apply LABLE; eauto. *)
  (*     unfold Genv.find_var_info in *. des_ifs. *)
  (*     i. eapply Mem.load_unchanged_on_1; try apply RO; eauto. *)
  (*     { admit "ez - Heq/genv_defs_range/NB". } *)
  (*     ii. exploit PERM0; eauto. i; des. inv ORD. *)
Qed.
Next Obligation.
  exploit SkEnv.project_spec_preserves_wf; eauto. intro WFSMALL.
  inv SKE. inv LE. inv WFSMALL.
  econs; eauto; swap 2 3.
  { congruence. }
  { etrans; eauto. rewrite NEXT. refl. }
  (* - ii. *)
  (*   unfold Genv.find_var_info in *. des_ifs. *)
  (*   exploit DEFSYMB; eauto. i; des. *)
  (*   destruct (classic (defs0 id)); cycle 1. *)
  (*   { exploit SYMBDROP; eauto. i; des. clarify. } *)
  (*   exploit SYMBKEEP; eauto. i; des. rewrite H in *. symmetry in H1. *)
  (*   inv WF. *)
  (*   exploit SYMBDEF0; eauto. intro DEF; des. *)
  (*   exploit DEFKEEP; eauto. *)
  (*   { eapply Genv.find_invert_symbol; eauto. } *)
  (*   intro DEF2; des. rewrite DEF in *. clarify. *)
  (*   exploit RO; eauto. *)
  (*   { rewrite DEF. ss. } *)
  (*   i; des. *)
  (*   esplits; eauto. *)

  (*   clear - LABLE SYMBKEEP. *)
  (*   destruct gv; ss. clear_tac. revert LABLE. generalize (0%Z) as ofs. i. *)
  (*   ginduction gvar_init; ii; ss. *)
  (*   des_ifs; des; esplits; eauto. *)
  (*   rewrite SYMBKEEP; eauto. *)
  (*   admit "hard - we need good_prog". *)
  - bar. move ROMATCH at bottom.
    ii.
    exploit (ROMATCH b id ab); eauto.
    { admit "ez". }
    { admit "ez". }
    i; des.
    esplits; et.
    eapply bmatch_proj; et.
    { admit "ez". }
    { i. clarify. admit "we need good-prog". }
    { i. clarify. admit "we need good-prog". }
  (* - (** copied from above **) *)
  (*   ii. *)
  (*   unfold Genv.find_var_info in *. des_ifs. *)
  (*   (* exploit DEFSYMB; eauto. i; des. *) *)
  (*   destruct (classic (defs0 id)); cycle 1. *)
  (*   { exploit SYMBDROP; eauto. i; des. clarify. } *)
  (*   exploit SYMBKEEP; eauto. i; des. rewrite SYMB in *. symmetry in H0. *)
  (*   inv WF. *)
  (*   exploit SYMBDEF0; eauto. intro DEF; des. *)
  (*   exploit DEFKEEP; eauto. *)
  (*   { eapply Genv.find_invert_symbol; eauto. } *)
  (*   intro DEF2; des. rewrite DEF in *. clarify. *)

  (*   assert(BCLINK: exists bc_link, genv_match bc_link skenv_link /\ *)
  (*                                  <<IMG: bc_link.(bc_img) = (fun blk => *)
  (*                                                               match (Genv.invert_symbol skenv_link blk) with *)
  (*                                                               | Some id => BCglob id *)
  (*                                                               | _ => BCother *)
  (*                                                               end)>>). *)
  (*   { unshelve eexists (BC (fun blk => match (Genv.invert_symbol skenv_link blk) with *)
  (*                                      | Some id => BCglob id *)
  (*                                      | _ => BCother *)
  (*                                      end) _ _); cycle 2. *)
  (*     { unfold genv_match. s. split; cycle 1. *)
  (*       { refl. } *)
  (*       split. *)
  (*       - split; intro T. *)
  (*         + apply Genv.find_invert_symbol in T. des_ifs. *)
  (*         + des_ifs. apply Genv.invert_find_symbol in Heq. des_ifs. *)
  (*       - i. *)
  (*         split; des_ifs. *)
  (*     } *)
  (*     { ss. ii. des_ifs. } *)
  (*     { ss. ii. des_ifs. apply_all_once Genv.invert_find_symbol. congruence. } *)
  (*   } *)
  (*   des. *)
  (*   eapply bmatch_incr with (bc2 := bc_link). *)
  (*   eapply BMATCH; try apply BCLINK; eauto. *)
  (*   { rewrite IMG. apply Genv.find_invert_symbol in H0. des_ifs. } *)
  (*   { rewrite DEF. ss. } *)
  (*   { rr. rr in GMATCH. des. esplits; ss; eauto. *)
  (*     - i. etrans; cycle 1. *)
  (*       { eapply GMATCH. } *)
        
  (*   } *)

  (*   exploit RO; eauto. *)
  (*   { rewrite DEF. ss. } *)
  (*   i; des. *)
  (*   esplits; eauto. *)

  (*   exploit BMATCH; eauto. *)
  (*   { rewrite DEF. ss. } *)
  (*   i; des. *)
  (*   esplits; eauto. *)
  (*   clear - LABLE SYMBKEEP. *)
  (*   destruct gv; ss. clear_tac. revert LABLE. generalize (0%Z) as ofs. i. *)
  (*   ginduction gvar_init; ii; ss. *)
  (*   des_ifs; des; esplits; eauto. *)
  (*   rewrite SYMBKEEP; eauto. *)
  (*   admit "hard - we need good_prog". *)
  (* - ii. eapply BMATCH; eauto. *)
  (*   + *)
Qed.
Next Obligation.
  admit "system - this axiom should be removed in project-only-internals".
  (* split; i; inv H; ss. *)
  (* - econs; eauto. *)
  (*   i. eapply RO; eauto. *)
  (*   unfold Genv.find_var_info in *. des_ifs_safe. *)
  (*   unfold System.skenv in *. *)
  (*   apply_all_once Genv_map_defs_def. des. des_ifs. *)
  (* - econs; eauto. *)
  (*   i. eapply RO; eauto. *)
  (*   unfold Genv.find_var_info in *. des_ifs_safe. *)
  (*   unfold System.skenv. *)
  (*   eapply_all_once Genv_map_defs_def_inv. rewrite Heq. ss. *)
Qed.
Next Obligation.
  set (CTX := Val.mi_normal).
  des. rename H into VAL. rename H0 into VALS. rename H1 into MEM. rename H2 into WF.
  exploit (@external_call_mem_inject_gen CTX ef skenv0 skenv0 (Args.vs args0) (Args.m args0) tr v_ret m_ret
                                         (to_inj su0 (Args.m args0).(Mem.nextblock)) (Args.m args0) (Args.vs args0)); eauto.
  { unfold to_inj. r. esplits; ii; ss; des_ifs; eauto.
    - exfalso. eapply WF; eauto. inv SKE. rewrite PUB. admit "ez - H0".
    - exfalso. apply n; clear n. admit "ez - SKE/WF".
  }
  { eapply to_inj_mem; eauto. }
  { inv MEM. clear - NB VALS. abstr (Args.vs args0) vs_arg.
    ginduction vs_arg; ii; ss. inv VALS. econs; eauto. destruct a; ss.
    unfold to_inj. r in H1. destruct b0; ss; cycle 1.
    { econs; eauto. }
    hexploit H1; ss; eauto.  i.
    econs; eauto.
    - des. des_ifs. rewrite NB in *. ss.
    - rewrite Ptrofs.add_zero. ss.
  }
  intro AX; des.
  hexploit external_call_nextblock; try apply EXT; eauto. intro NBEXT.
  exists (to_su f' su0.(ge_nb) m_ret.(Mem.nextblock)). unfold to_su.
  esplits; eauto.
  - eapply hle_old_hle. r. s.
    unfold to_inj in AX4, AX5. r in AX4. r in AX5.
    esplits; eauto.
    + ii.
      inv MEM. exploit BOUND; eauto. i. des_ifs; cycle 1.
      { unfold Mem.valid_block in *. inv AX2. xomega. }
      destruct p0; ss.
      exploit AX5; eauto.
      { des_ifs. }
      i; des.
      ss.
    + ii. des. des_ifs.
      rename x0 into bb.
      apply NNPP. ii.
      exploit (AX4 bb bb); eauto; i; clarify.
      des_ifs. exfalso.
      eapply n. eapply Plt_Ple_trans; et. inv MEM. rewrite NB. xomega.
    + inv MEM. rewrite NB. inv AX2; ss.
  - r. s. esplits; eauto.
    + s. r. ii; ss. clarify. inv AX0. des_ifs.
    + inv AX1. apply NNPP. ii. exploit mi_freeblocks; eauto. i; clarify. inv AX0; ss. clarify.
  - s. econs; cycle 1; ss; eauto.
    { ii. des_ifs. }
    { inv MEM. etrans; eauto. }
    { ii. clarify. exploit Mem.perm_valid_block; eauto. i. unfold Mem.valid_block in H. des_ifs_safe.
      inv AX1. inv mi_inj. destruct p0; ss. exploit mi_memval; eauto. intro MV.
      rewrite PTR in *. inv MV. inv H1. des_ifs_safe.
      exploit mi_freeblocks; eauto. i; clarify.
    }
  - econs; eauto; ss.
    + i. des_ifs.
      assert((to_inj su0 (Mem.nextblock (Args.m args0))) x0 = None).
      { destruct (to_inj su0 (Mem.nextblock (Args.m args0)) x0) eqn:T; ss. destruct p0; ss.
        exploit (AX4 x0); eauto. i. clarify. }
      unfold to_inj in H. des_ifs.
      { inv WF. eauto. }
      inv MEM. etrans; eauto. xomega.
    + i. des_ifs.
  - econs; eauto.
    + ii; ss. eapply external_call_max_perm; try apply EXT; eauto.
    + ii; ss. eapply external_call_readonly; try apply EXT; eauto.
    + eapply Mem.unchanged_on_implies; eauto.
      unfold flip in *. ii; ss.
      rr. unfold to_inj. des_ifs.
Qed.


Local Opaque Z.mul Z.add Z.sub Z.div.
Local Transparent Mem.load.
Lemma mem'_load_val'
      su m0
      (MEM: mem' su m0)
      chunk blk ofs v
      (PUB: ~ su blk)
      (LOAD: Mem.load chunk m0 blk ofs = Some v)
  :
    <<VAL: val' su v>>
.
Proof.
  inv MEM.
  unfold Mem.load in *. des_ifs. ii.
  hexploit SOUND; eauto.
  { eapply Mem.valid_access_perm; et. }
  intro MV; des.
  unfold decode_val in *.
  Local Opaque Mem.getN.
  des_ifs; cbn in *; unfold Pos.to_nat in *; ss.
  -
    (* Local Opaque ZMap.get. *)
    ss. des_ifs.
    unfold proj_value in *. des_ifs.
    ss.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    clear_tac.
    Local Transparent Mem.getN. ss. clarify.
    specialize (SOUND blk ofs PUB).
    exploit MV; eauto.
  - ss. des_ifs.
  - Local Opaque Mem.getN.
    unfold proj_value in *. des_ifs.
    ss.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    bsimpl. des_safe. des_sumbool. clarify. repeat (destruct n; ss; []). des_ifs_safe.
    clear_tac.
    Local Transparent Mem.getN. ss. clarify.
    specialize (SOUND blk ofs PUB).
    exploit MV; eauto.
Qed.

Local Transparent Mem.loadbytes.
Lemma mem'_loadbytes_val'
      su m0
      (MEM: mem' su m0)
      blk ofs v q n
      (PUB: ~ su blk)
      (LOAD: Mem.loadbytes m0 blk ofs 1 = Some [Fragment v q n])
  :
    <<VAL: val' su v>>
.
Proof.
  inv MEM.
  unfold Mem.loadbytes in *. des_ifs. ii. clarify.
  hexploit (SOUND blk ofs); eauto.
  { eapply r. xomega. }
  intro MV; des.
  rewrite H0 in *. exploit MV; eauto.
Qed.

Lemma val_le
      su0 su1 v
      (SU: val' su1 v)
      (LE: le' su0 su1)
      (NB: Ple (Unreach.nb su1) (Unreach.nb su0))
  :
    <<SU: val' su0 v>>
.
Proof.
  ii. clarify. exploit SU; eauto. i; des. esplits; eauto.
  - ii. eapply H. rr in LE. des.
    eapply PRIV; eauto.
  - rr in LE. des. xomega.
Qed.

Lemma memval_le
      su0 su1 mv
      (SU: memval' su1 mv)
      (LE: le' su0 su1)
      (NB: Ple (Unreach.nb su1) (Unreach.nb su0))
  :
    <<SU: memval' su0 mv>>
.
Proof.
  ii. clarify. exploit SU; eauto. i; des. esplits; eauto.
  - ii. eapply H. rr in LE. des.
    eapply PRIV; eauto.
  - rr in LE. des. xomega.
Qed.

