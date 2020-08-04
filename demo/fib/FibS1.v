Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC MemoryC Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require ClightC.
Require Import FibHeader.
Require Import Fib0.
Require Import SIR.
(* Require Import Clightdefs. *)

Set Implicit Arguments.



Fixpoint taus {E R} (n: nat) (it: itree E R): itree E R :=
  match n with
  | O => it
  | S m => tau;; (taus m it)
  end
.

Notation "n taus;; t2" := (taus n t2)
  (at level 61, right associativity) : itree_scope.

Definition f_fib (oh0: owned_heap) (m0: mem) (vs0: list val):
  itree (E owned_heap) (owned_heap * (mem * val)) :=
  n <- unwrapU (parse_arg oh0 m0 vs0) ;;
  x <- trigger (EChoose nat) ;;
  x taus;;
  Ret (oh0, (m0, Vint (of_nat (fib_nat n))))
.

Definition prog: program owned_heap :=
  (Maps.add _fib f_fib Maps.empty).

Program Definition module: SMod.t _ := SMod.mk (Fib0.module) prog "fib"%string initial_owned_heap _.
