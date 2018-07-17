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
Require Un_Territoire_S.
Module Un_Etre_humain_S.
  Definition est_un_adulte (abst_T : Set) (abst_age : basics.int__t)
    (s : abst_T) : basics.bool__t := (basics._gt__equal_ abst_age 18).
  Definition est_un_mineur (abst_T : Set) (abst_age : basics.int__t)
    (s : abst_T) : basics.bool__t := (basics._lt_ abst_age 18).
  
  (* From species Un_Etre_humain_S#Un_Etre_humain_S. *)
  (* Section for proof of theorem 'est_une_femme_ou_un_homme_th'. *)
  Section Proof_of_est_une_femme_ou_un_homme_th.
    Variable abst_T : Set.
    Variable abst_est_un_homme : abst_T -> basics.bool__t.
    Variable abst_est_une_femme : abst_T -> basics.bool__t.
    Hypothesis abst_est_un_homme_ou_une_femme_pr :
      forall s : abst_T,
        Is_true ((abst_est_un_homme s)) ->
          ~Is_true (((abst_est_une_femme s))).
(* File "Un_Etre_humain_S.fcl", line 28, characters 19-59 *)
Theorem for_zenon_est_une_femme_ou_un_homme_th : (forall s : abst_T, ((Is_true (abst_est_une_femme s))->(~(Is_true (abst_est_un_homme s))))).
Proof.
apply NNPP. intro zenon_G.
apply (zenon_notallex_s (fun s : abst_T => ((Is_true (abst_est_une_femme s))->(~(Is_true (abst_est_un_homme s))))) zenon_G); [ zenon_intro zenon_H2; idtac ].
elim zenon_H2. zenon_intro zenon_Ts_d. zenon_intro zenon_H4.
apply (zenon_notimply_s _ _ zenon_H4). zenon_intro zenon_H6. zenon_intro zenon_H5.
apply zenon_H5. zenon_intro zenon_H7.
generalize (abst_est_un_homme_ou_une_femme_pr zenon_Ts_d). zenon_intro zenon_H8.
apply (zenon_imply_s _ _ zenon_H8); [ zenon_intro zenon_Ha | zenon_intro zenon_H9 ].
exact (zenon_Ha zenon_H7).
exact (zenon_H9 zenon_H6).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_est_une_femme_ou_un_homme_th :
      forall s : abst_T,
        Is_true ((abst_est_une_femme s)) ->
          ~Is_true (((abst_est_un_homme s))).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_est_un_homme := abst_est_un_homme).
    assert (__force_use_abst_est_une_femme := abst_est_une_femme).
    assert (__force_use_abst_est_un_homme_ou_une_femme_pr :=
      abst_est_un_homme_ou_une_femme_pr).
    apply for_zenon_est_une_femme_ou_un_homme_th;
    auto.
    Qed.
    End Proof_of_est_une_femme_ou_un_homme_th.
  
  Theorem est_une_femme_ou_un_homme_th  (abst_T : Set)
    (abst_est_un_homme : abst_T -> basics.bool__t)
    (abst_est_une_femme : abst_T -> basics.bool__t)
    (abst_est_un_homme_ou_une_femme_pr :
    forall s : abst_T,
      Is_true ((abst_est_un_homme s)) -> ~Is_true (((abst_est_une_femme s)))):
    forall s : abst_T,
      Is_true ((abst_est_une_femme s)) -> ~Is_true (((abst_est_un_homme s))).
  apply for_zenon_abstracted_est_une_femme_ou_un_homme_th;
  auto.
  Qed.
  
  (* From species Un_Etre_humain_S#Un_Etre_humain_S. *)
  (* Section for proof of theorem 'est_un_adulte_ou_un_mineur_th'. *)
  Section Proof_of_est_un_adulte_ou_un_mineur_th.
    Variable abst_T : Set.
    Variable abst_est_un_adulte : abst_T -> basics.bool__t.
    Variable abst_est_un_mineur : abst_T -> basics.bool__t.
    Hypothesis abst_est_un_adulte_ou_un_mineur_pr :
      forall s : abst_T,
        Is_true ((abst_est_un_adulte s)) \/ Is_true ((abst_est_un_mineur s)).
(* File "Un_Etre_humain_S.fcl", line 43, characters 18-59 *)
Theorem for_zenon_est_un_adulte_ou_un_mineur_th : (forall s : abst_T, ((Is_true (abst_est_un_adulte s))\/(Is_true (abst_est_un_mineur s)))).
Proof.
apply NNPP. intro zenon_G.
exact (zenon_G abst_est_un_adulte_ou_un_mineur_pr).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_est_un_adulte_ou_un_mineur_th :
      forall s : abst_T,
        Is_true ((abst_est_un_adulte s)) \/ Is_true ((abst_est_un_mineur s)).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_est_un_adulte := abst_est_un_adulte).
    assert (__force_use_abst_est_un_mineur := abst_est_un_mineur).
    assert (__force_use_abst_est_un_adulte_ou_un_mineur_pr :=
      abst_est_un_adulte_ou_un_mineur_pr).
    apply for_zenon_est_un_adulte_ou_un_mineur_th;
    auto.
    Qed.
    End Proof_of_est_un_adulte_ou_un_mineur_th.
  
  Theorem est_un_adulte_ou_un_mineur_th  (abst_T : Set)
    (abst_est_un_adulte : abst_T -> basics.bool__t)
    (abst_est_un_mineur : abst_T -> basics.bool__t)
    (abst_est_un_adulte_ou_un_mineur_pr :
    forall s : abst_T,
      Is_true ((abst_est_un_adulte s)) \/ Is_true ((abst_est_un_mineur s))):
    forall s : abst_T,
      Is_true ((abst_est_un_adulte s)) \/ Is_true ((abst_est_un_mineur s)).
  apply for_zenon_abstracted_est_un_adulte_ou_un_mineur_th;
  auto.
  Qed.
  
End Un_Etre_humain_S.

