Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Smallstep.
Require Import GlobalenvsC.
Require Import LinkingC.
Require Import CoqlibC.
Require Import sflib.

Require Import ModSem Mod Skeleton System.
Require Export Syntax.

Set Implicit Arguments.







Definition Midx := nat.

Module Frame.

  Record t: Type := mk {
    ms: ModSem.t;
    st: ms.(ModSem.state); (* local state *)
    midx: Midx;
  }.

  Definition update_st (fr0: t) (st0: fr0.(ms).(ModSem.state)): t := (mk fr0.(ms) st0 fr0.(midx)).

End Frame.



Module Ge.

  (* NOTE: Ge.(snd) is not used in semantics. It seems it is just for convenience in meta theory *)
  Definition t: Type := (list ModSem.t * SkEnv.t).

  (* TODO: remove redundancy? ms, midx *)
  Inductive find_fptr_owner (ge: t) (fptr: val) (ms: ModSem.t) (midx: Midx): Prop :=
  | find_fptr_owner_intro
      (MODSEM: List.nth_error (fst ge) midx = Some ms)
      if_sig
      (INTERNAL: Genv.find_funct ms.(ModSem.skenv) fptr = Some (Internal if_sig)).

  Inductive disjoint (ge: t): Prop :=
  | disjoint_intro
      (DISJOINT: forall fptr ms0 ms1 midx0 midx1
          (FIND0: ge.(find_fptr_owner) fptr ms0 midx0)
          (FIND1: ge.(find_fptr_owner) fptr ms1 midx1),
          ms0 = ms1 /\ midx0 = midx1).

End Ge.

Inductive state: Type :=
| Callstate
    (args: Args.t)
    (frs: list Frame.t)
    (* Note: I tried `(ohs: Midx -> option { oh: Type & oh })` (HList) because it seemed easier to typecheck, *)
    (* but actually the typecheck failed in "step" *)
    (* Note: List module does not have update method, *)
    (* so I use functional style (which is easier to define my own "update" function) *)
    (msohs: Midx -> option { ms: ModSem.t & ms.(ModSem.owned_heap) })
| State
    (frs: list Frame.t)
    (msohs: Midx -> option { ms: ModSem.t & ms.(ModSem.owned_heap) })
.

(* Definition get_ohs (st: state): Midx -> option { ms: ModSem.t & ms.(ModSem.owned_heap) } := *)
(*   match st with *)
(*   | Callstate _ _ ohs => ohs *)
(*   | State _ ohs => ohs *)
(*   end. *)

Definition update Y (map: Midx -> Y) (x: Midx) (y: Y): Midx -> Y := fun n => if Nat.eq_dec x n then y else map x.

Inductive step (ge: Ge.t): state -> trace -> state -> Prop :=
| step_call
    fr0 frs args oh msohs0 msohs1 
    (AT: fr0.(Frame.ms).(ModSem.at_external) fr0.(Frame.st) oh args)
    (MSOHS: msohs1 = update msohs0 fr0.(Frame.midx) (Some (existT _ _ oh))):
    step ge (State (fr0 :: frs) msohs0)
         E0 (Callstate args (fr0 :: frs) msohs1)

| step_init
    args frs ms midx st_init oh msohs
    (MSFIND: ge.(Ge.find_fptr_owner) (Args.get_fptr args) ms midx)
    (OH: msohs midx = Some (existT _ _ oh))
    (INIT: ms.(ModSem.initial_frame) oh args st_init):
    step ge (Callstate args frs msohs)
         E0 (State ((Frame.mk ms st_init midx) :: frs) msohs)

| step_internal
    fr0 frs tr st0 msohs
    (STEP: Step (fr0.(Frame.ms)) fr0.(Frame.st) tr st0):
    step ge (State (fr0 :: frs) msohs)
         tr (State (((Frame.update_st fr0) st0) :: frs) msohs)
| step_return
    fr0 fr1 frs retv st0 msohs0 msohs1 oh0 oh1
    (FINAL: fr0.(Frame.ms).(ModSem.final_frame) fr0.(Frame.st) oh0 retv)
    (AFTER: fr1.(Frame.ms).(ModSem.after_external) fr1.(Frame.st) oh1 retv st0)
    (MSOHS: msohs1 = update msohs0 fr0.(Frame.midx) (Some (existT _ _ oh0)))
    (OH: msohs1 fr1.(Frame.midx) = Some (existT _ _ oh1)):
    step ge (State (fr0 :: fr1 :: frs) msohs0)
         E0 (State (((Frame.update_st fr1) st0) :: frs) msohs1)
.




Section SEMANTICS.

  Variable p: program.

  Definition link_sk: option Sk.t := link_list (List.map Mod.sk p).

  Definition skenv_fill_internals (skenv: SkEnv.t): SkEnv.t :=
    (Genv_map_defs skenv) (fun _ gd => Some
                                      match gd with
                                      | Gfun (External ef) => (Gfun (Internal (ef_sig ef)))
                                      | Gfun _ => gd
                                      | Gvar gv => gd
                                      end).

  Definition load_system (skenv: SkEnv.t): (ModSem.t * SkEnv.t) :=
    (System.modsem skenv, (skenv_fill_internals skenv)).

  Definition load_modsems (skenv: SkEnv.t): list ModSem.t := List.map ((flip Mod.modsem) skenv) p.

  Definition load_genv (init_skenv: SkEnv.t): Ge.t :=
    let (system, skenv) := load_system init_skenv in
    (system :: (load_modsems init_skenv), init_skenv).

  Definition load_owned_heaps (ge: Ge.t): Midx -> option { ms: ModSem.t & ms.(ModSem.owned_heap) } :=
    List.nth_error (map (fun ms => (existT _ ms ms.(ModSem.initial_owned_heap))) (fst ge))
  .

  (* Making dummy_module that calls main? => Then what is sk of it? Memory will be different with physical linking *)
  Inductive initial_state (ge: Ge.t): state -> Prop :=
  | initial_state_intro
      sk_link skenv_link m_init fptr_init msohs
      (INITSK: link_sk = Some sk_link)
      (INITSKENV: (Sk.load_skenv sk_link) = skenv_link)
      (INITMEM: (Sk.load_mem sk_link) = Some m_init)
      (FPTR: fptr_init = (Genv.symbol_address skenv_link sk_link.(prog_main) Ptrofs.zero))
      (SIG: (Genv.find_funct skenv_link) fptr_init = Some (Internal signature_main))
      (WF: forall md (IN: In md p), <<WF: Sk.wf md>>)
      (MSOHS: msohs = load_owned_heaps ge):
      initial_state ge (Callstate (Args.mk fptr_init [] m_init) [] msohs).

  Inductive final_state: state -> int -> Prop :=
  | final_state_intro
      fr0 oh msohs retv i
      (FINAL: fr0.(Frame.ms).(ModSem.final_frame) fr0.(Frame.st) oh retv)
      (INT: (Retv.v retv) = Vint i):
      final_state (State [fr0] msohs) i.

  Definition sem: semantics :=
    let ge := (match link_sk with
                    | Some sk_link => load_genv (Sk.load_skenv sk_link)
                    | None => (nil, SkEnv.empty)
                    end) in
    (Semantics_gen (fun _ => step) (initial_state ge) final_state
                   ge 
                   (* NOTE: The symbolenv here is never actually evoked in our semantics. Putting this value is merely for our convenience. (lifting receptive/determinate) Whole proof should be sound even if we put dummy data here. *)
                   (match link_sk with
                    | Some sk_link => (Sk.load_skenv sk_link)
                    | None => SkEnv.empty
                    end)).

  (* Note: I don't want to make it option type. If it is option type, there is a problem. *)
  (* I have to state this way:
```
Variable sem_src: semantics.
Hypothesis LOADSRC: load p_src = Some sem_src.
```
Then, sem_src.(state) is not evaluatable.
   *)
  (* However, if it is not option type.
```
Let sem_src := semantics prog.
```
Then, sem_src.(state) is evaluatable.
   *)

End SEMANTICS.

Hint Unfold link_sk load_modsems load_genv.
