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
Require strict_orders.
Require Un_Contrat_intelligent_S.
Require Une_Phrase_d_un_paragraphe_S.
Module Un_Bloc_S.
  Definition l_ordinal_est_non_negatif (abst_T : Set)
    (abst_l_ordinal : abst_T -> basics.int__t) (blo : abst_T) :
    basics.bool__t := (basics._gt__equal_ (abst_l_ordinal blo) 0).
  Definition l_ordinal_est_positif (abst_T : Set)
    (abst_l_ordinal : abst_T -> basics.int__t) (blo : abst_T) :
    basics.bool__t := (basics._gt_ (abst_l_ordinal blo) 0).
  
End Un_Bloc_S.

