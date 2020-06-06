From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     (* Data.String *)
     (* Structures.Monad *)
     (* Structures.Traversable *)
     (* Structures.Foldable *)
     (* Structures.Reducible *)
     Structures.Maps
     (* Data.List *)
.

From ITree Require Export
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
.

Export SumNotations.
Export ITreeNotations.
Export Monads.
Export MonadNotation.

Require Import MapsC.
Require Import ValuesC.
Require Import MemoryC.
Require Import CoqlibC.
Require Import ASTC.
Require Import EventsC.
Require Import GlobalenvsC.
Require Import IntegersC.
Require Import Mod ModSem Any Skeleton.

Require Import Program.

Set Implicit Arguments.



Instance function_Map (K V: Type) (dec: forall k0 k1, {k0=k1} + {k0<>k1}): (Map K V (K -> option V)) :=
  Build_Map
    (fun _ => None)
    (fun k0 v m => fun k1 => if dec k0 k1 then Some v else m k1)
    (fun k0 m => fun k1 => if dec k0 k1 then None else m k1)
    (fun k m => m k)
    (fun m0 m1 => fun k => match (m0 k) with
                           | Some v => Some v
                           | _ => m1 k
                           end)
.


Section OWNEDHEAP.
Variable owned_heap: Type.

Section EFF.

  Variant LocalE: Type -> Type :=
  | LGet (x: ident): LocalE val
  | LPut (x: ident) (v: val): LocalE unit
  | LPush: LocalE unit
  | LPop: LocalE unit
  .

  Definition MemE: Type -> Type := stateE mem.

  Definition OwnedHeapE: Type -> Type := stateE owned_heap.

  (*** In shallow embedding, one may directly access globalenv.
       However, we may want to restrict its access (e.g., not allowing sth like "Genv.find_symbol x == 42")
       so that one may prove commutativity/unusedglob/etc.
   ***)
  Variant GlobalE: Type -> Type :=
  | GFindS (x: ident) : GlobalE val
  .

  Variant InternalCallE: Type -> Type :=
  | ICall (name: ident) (vs: list val): InternalCallE val
  .

  Variant ExternalCallE: Type -> Type :=
  | ECall (fptr: val) (vs: list val): ExternalCallE (val)
  .

  Variant EventE: Type -> Type :=
  | ENB (msg: string): EventE void
  | EUB (msg: string): EventE void
  | ESyscall (ef: external_function) (args: list val): EventE (val)
  | EDone (v: val): EventE void
  .

  Definition eff0: Type -> Type := Eval compute in ExternalCallE +' EventE.
  Definition eff1: Type -> Type := Eval compute in OwnedHeapE +' eff0.
  Definition eff2: Type -> Type := Eval compute in MemE +' eff1.
  Definition eff3: Type -> Type := Eval compute in GlobalE +' eff2.
  Definition eff4: Type -> Type := Eval compute in LocalE +' eff3.
  Definition eff5: Type -> Type := Eval compute in InternalCallE +' eff4.
  Definition E := Eval compute in eff5.

End EFF.

(* Q: Why manually match "void" type, not using "embed" or "trigger"?
   A: It returns arbitrary type "A", not "void" *)
Definition triggerUB {E A} `{EventE -< E} (msg: string): itree E A :=
  vis (EUB msg) (fun v => match v: void with end)
.
Definition triggerNB {E A} `{EventE -< E} (msg: string) : itree E A :=
  vis (ENB msg) (fun v => match v: void with end)
.
Definition triggerDone {E A} `{EventE -< E} (v: val): itree E A :=
  vis (EDone v) (fun v => match v: void with end)
.

Definition unwrapN {E X} `{EventE -< E} (x: option X): itree E X :=
  match x with
  | Some x => ret x
  | None => triggerNB "unwrap"
  end.

Definition unwrapU {E X} `{EventE -< E} (x: option X): itree E X :=
  match x with
  | Some x => ret x
  | None => triggerUB "unwrap"
  end.







Record function : Type := mkfunction
  { fn_sig: signature;
    fn_code: (forall (vs: list val), itree eff5 val); }
.

Definition program: Type := AST.program (fundef function) unit.



Section DENOTE.

  Variable p: program.
  Variable ge: SkEnv.t.

  Definition denote_function: (InternalCallE ~> itree eff5) :=
    fun T ei =>
      let '(ICall func_name vs) := ei in
      match (find (fun nf => ident_eq func_name (fst nf)) p.(prog_defs)) with
      | Some (_, Gfun (Internal f)) =>
      (* match (prog_defmap p) ! func_name with *)
      (* | Some (Gfun (Internal f)) => *)
        trigger LPush ;;
        retv <- (f.(fn_code) vs) ;;
        trigger LPop ;;
        Ret retv
        (* trigger LPush ;; *)
        (*         retv <- f.(fn_code) ei ;; *)
        (*         trigger LPop ;; *)
        (*         Ret retv *)
      | _ => triggerNB "TODO: UB? NB? Which one is useful?"
      end
  .

  Instance lenv_Map: (Map ident val (ident -> option val)) := function_Map val Pos.eq_dec.
  Definition lenv := list (ident -> option val).
  Definition handle_LocalE {E: Type -> Type} `{EventE -< E}: LocalE ~> stateT lenv (itree E) :=
    fun _ e le =>
      let hd: ident -> option val := hd Maps.empty le in
      let tl: lenv := tl le in
      match e with
      | LGet x => v <- unwrapN (*** TODO: U? N? ***) (Maps.lookup x hd) ;; Ret (le, v)
      | LPut x v => Ret ((Maps.add x v hd) :: tl, tt)
      | LPush => Ret (Maps.empty :: hd :: tl, tt)
      | LPop => Ret (tl, tt)
      end.

  Definition interp_LocalE {E A} `{EventE -< E} (t : itree (LocalE +' E) A): (itree E) A :=
    let t': stateT lenv (itree E) A := interp_state (case_ handle_LocalE pure_state) t in
    '(_, a) <- t' nil ;; Ret a
  .

  Definition handle_GlobalE {E: Type -> Type} `{EventE -< E}: GlobalE ~> itree E :=
    fun _ e =>
      match e with
      | GFindS x => blk <- unwrapN (Genv.find_symbol ge x) ;; Ret (Vptr blk Ptrofs.zero)
      end
  .

  Definition interp_GlobalE {E A} `{EventE -< E} (t : itree (GlobalE +' E) A): itree E A :=
    interp (case_ (handle_GlobalE) (id_ _)) t
  .

  Definition denote_program: (InternalCallE ~> itree eff2) :=
    (* let sem0: (InternalCallE ~> itree eff0) := mrec denote_function in *)
    (* fun _ ic => *)
    (*   let sem1: itree eff1 _ := interp_GlobalE (sem0 _ ic) in *)
    (*   sem1 *)
    fun _ ic =>
      let sem4: itree eff4 _ := (mrec denote_function) _ ic in
      let sem3: itree eff3 _ := interp_LocalE sem4 in
      let sem2: itree eff2 _ := interp_GlobalE sem3 in
      sem2
  .

End DENOTE.



Section MODSEM.

  Variable mi: string.
  Variable skenv_link: SkEnv.t.
  Variable initial_owned_heap: owned_heap.
  Variable p: program.
  Let skenv: SkEnv.t := (SkEnv.project skenv_link) (Sk.of_program fn_sig p).
  (* Let ge: genv := (SkEnv.revive skenv) p. *)
  Definition genvtype: Type := unit.
  Let ge: genvtype := tt.

  Record state := mk {
    itr:> itree eff2 val;
    oh: owned_heap;
    m: mem;
  }.

  Let denote_program := denote_program p skenv.

  Inductive initial_frame (oh0: owned_heap) (args: Args.t): state -> Prop :=
  | initial_frame_intro
      fid blk m0 vs itr
      (SYMB: Genv.find_symbol skenv fid = Some blk)
      (FPTR: (Args.fptr args) = Vptr blk Ptrofs.zero)
      (VS: (Args.vs args) = vs)
      (M: (Args.m args) = m0)
      (DENOTE: denote_program (ICall fid vs) = itr)
    :
      initial_frame oh0 args (mk itr oh0 m0)
  .

  Inductive at_external (st0: state): owned_heap -> Args.t -> Prop :=
  | at_external_intro
      args fptr vs k
      (VIS: (observe st0) = VisF (subevent _ (ECall fptr vs)) k)
      (ARGS: args = Args.mk fptr vs st0.(m))
    :
      at_external st0 st0.(oh) args
  .

  Inductive get_k (st0: state): (val -> itree eff2 val) -> Prop :=
  | get_k_intro
      _vs _fptr k
      (VIS: (observe st0) = VisF (subevent _ (ECall _fptr _vs)) k)
    :
      get_k st0 k
  .

  Inductive after_external (st0: state) (oh0: owned_heap) (retv: Retv.t): state -> Prop :=
  | after_external_intro
      k m0 rv st1
      (GETK: get_k st0 k)
      (V: (Retv.v retv) = rv)
      (M: (Retv.m retv) = m0)
      (KONT: st1 = mk (k rv) oh0 m0)
    :
      after_external st0 oh0 retv st1
  .

  Inductive final_frame (st0: state): owned_heap -> Retv.t -> Prop :=
  | final_frame_intro
      oh0 m0 (rv: val) retv
      (RET: (observe st0) = RetF rv)
      (RETV: retv = Retv.mk rv m0)
      (M: m0 = st0.(m))
      (OH: oh0 = st0.(oh))
    :
      final_frame st0 oh0 retv
  .

  Inductive step (se: Senv.t) (ge: genvtype) (st0: state) (tr: trace) (st1: state): Prop :=
  | step_tau
      itr0 oh0 m0
      itr1
      (TAU: (observe itr0) = TauF itr1)

      (ST0: st0 = mk itr0 oh0 m0)
      (TR: tr = E0)
      (ST1: st1 = mk itr1 oh0 m0)
  (*** ub is stuck, so we don't state anything ***)
  | step_nb
      msg k
      (VIS: (observe st0) = VisF (subevent _ (ENB msg)) k)

      (TR: tr = E0)
  | step_syscall
      itr0 oh0 m0
      ef vs rv m1 k
      (VIS: (observe st0) = VisF (subevent _ (ESyscall ef vs)) k)
      (SYSCALL: external_call ef se vs m0 tr rv m1)

      (ST0: st0 = mk itr0 oh0 m0)
      (TR: tr = E0)
      (ST1: st1 = mk (k rv) oh0 m1)
  | step_done
      itr0 oh0 m0
      v k
      (VIS: (observe st0) = VisF (subevent _ (EDone v)) k)

      (ST0: st0 = mk itr0 oh0 m0)
      (TR: tr = E0)
      (ST1: st1 = mk (Ret v) oh0 m0)
  | step_mget
      itr0 oh0 m0
      k
      (VIS: (observe st0) = VisF (subevent _ (Get _)) k)

      (ST0: st0 = mk itr0 oh0 m0)
      (TR: tr = E0)
      (ST1: st1 = mk (k m0) oh0 m0)
  | step_mput
      itr0 oh0 m0
      m1 k
      (VIS: (observe st0) = VisF (subevent _ (Put _ m1)) k)

      (ST0: st0 = mk itr0 oh0 m0)
      (TR: tr = E0)
      (ST1: st1 = mk (k tt) oh0 m1)
  | step_ohget
      itr0 oh0 m0
      k
      (VIS: (observe st0) = VisF (subevent _ (Get _)) k)

      (ST0: st0 = mk itr0 oh0 m0)
      (TR: tr = E0)
      (ST1: st1 = mk (k oh0) oh0 m0)
  | step_ohput
      itr0 oh0 m0
      oh1 k
      (VIS: (observe st0) = VisF (subevent _ (Put _ oh1)) k)

      (ST0: st0 = mk itr0 oh0 m0)
      (TR: tr = E0)
      (ST1: st1 = mk (k tt) oh1 m0)
  .

  Program Definition modsem: ModSem.t :=
    {| ModSem.step := step;
       ModSem.owned_heap := owned_heap;
       ModSem.at_external := at_external;
       ModSem.initial_frame := initial_frame;
       ModSem.final_frame := final_frame;
       ModSem.after_external := after_external;
       ModSem.initial_owned_heap := initial_owned_heap;
       ModSem.globalenv := ge;
       ModSem.skenv := skenv;
       ModSem.skenv_link := skenv_link;
       ModSem.midx := Some mi;
    |}.
  Next Obligation.
    inv AT0. inv AT1. rewrite VIS in *. clarify.
  Qed.
  Next Obligation.
    inv FINAL0. inv FINAL1. rewrite RET in *. clarify.
  Qed.
  Next Obligation.
    inv AFTER0. inv AFTER1. inv GETK. inv GETK0. rewrite VIS in *.
    ss. clarify. simpl_depind. clarify.
  Qed.
  Next Obligation.
    ii. des. inv PR; ss. inv PR0; ss; clarify; try rewrite VIS in *; ss; clarify.
  Qed.
  Next Obligation.
    ii. des. inv PR0; ss. inv PR; ss; clarify; try rewrite RET in *; ss; clarify.
  Qed.
  Next Obligation.
    ii. des. inv PR; ss. inv PR0; ss; clarify; try rewrite VIS in *; ss; clarify.
  Qed.

End MODSEM.

Program Definition module (p: program) (mi: string) (initial_owned_heap: SkEnv.t -> owned_heap): Mod.t :=
  {| Mod.data := p; Mod.get_sk := (Sk.of_program fn_sig);
     Mod.get_modsem := fun skenv_link p => modsem mi skenv_link
                                                  (initial_owned_heap skenv_link) p;
     Mod.midx := Some mi |}
.

End OWNEDHEAP.

