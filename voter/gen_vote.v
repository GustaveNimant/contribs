(* Coq >= 8.3pl2: disable automatic introduction of hypotheses. *)
Global Unset Automatic Introduction.
(* Coq >= 8.5: allow sum constructors without explicit types in patterns. *)
Global Set Asymmetric Patterns.
Require Import zenon.
Require Import zenon_induct.
Require Import zenon_focal.
Require Export Bool.
Require Export ZArith.
Open Scope Z_scope.
Require Export Reals.
Require Export Ascii.
Require Export String.
Require Export List.
Require Import Wellfounded.
Require Export Recdef.
Require Export coq_builtins.
Require Import Relations.
Require Import Zwf.

(* Below: to prevent Function to apply heuristics that would
the expected aim in recursive functions termination proofs. *)

Set Function_raw_tcc.

Require basics.
Require sets.
Require orders.
Require gen_value.
Require gen_diag.
Module Gen_voter.
  Definition diag (_p_V_T : Set) (_p_S_T : Set)
    (p : (Datatypes.prod _p_V_T _p_S_T)) : _p_S_T := ((basics.snd _ _) p).
  Definition value (_p_V_T : Set) (_p_S_T : Set)
    (p : (Datatypes.prod _p_V_T _p_S_T)) : _p_V_T := ((basics.fst _ _) p).
  Definition compatible (_p_V_T : Set) (_p_S_T : Set)
    (_p_V_consistency_rule : _p_V_T -> _p_V_T -> basics.bool__t)
    (_p_S_valid : _p_S_T -> basics.bool__t)
    (abst_diag : (Datatypes.prod _p_V_T _p_S_T) -> _p_S_T)
    (abst_value : (Datatypes.prod _p_V_T _p_S_T) -> _p_V_T)
    (s1 : (Datatypes.prod _p_V_T _p_S_T))
    (s2 : (Datatypes.prod _p_V_T _p_S_T)) : coq_builtins.prop__t :=
    (Is_true ((_p_S_valid (abst_diag s1))) /\
       Is_true ((_p_S_valid (abst_diag s2))) /\
         Is_true ((_p_V_consistency_rule (abst_value s1) (abst_value s2)))) \/
      (~Is_true (((_p_S_valid (abst_diag s1)))) /\
         ~Is_true (((_p_S_valid (abst_diag s2))))).
  
End Gen_voter.

