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
Require etat_vote.
Require num_capteur.
Require diag.
Require pair.
Require gen_vote.
Module Voteur.
  Definition sensor (_p_C_T : Set) (_p_P_T : Set) (_p_P_prj_a :
    _p_P_T -> _p_C_T) (diag : _p_P_T) : _p_C_T := (_p_P_prj_a diag).
  Definition state (_p_E_T : Set) (_p_P_T : Set) (_p_P_prj_b :
    _p_P_T -> _p_E_T) (diag : _p_P_T) : _p_E_T := (_p_P_prj_b diag).
  
  (* From species vote#Voteur. *)
  (* Section for proof of theorem 't1'. *)
  Section Proof_of_t1.
    Variable _p_E_T : Set.
    Variable _p_V_T : Set.
    Variable _p_P_T : Set.
    Variable _p_E_equal : _p_E_T -> _p_E_T -> basics.bool__t.
    Variable _p_E_no_match : _p_E_T.
    Variable _p_E_partial_match : _p_E_T.
    Variable _p_E_perfect_match : _p_E_T.
    Variable _p_E_range_match : _p_E_T.
    Variable _p_E_all_value :
      forall e : _p_E_T,
        (Is_true ((_p_E_equal e _p_E_no_match)) \/
           Is_true ((_p_E_equal e _p_E_range_match)) \/
             Is_true ((_p_E_equal e _p_E_partial_match)) \/
               Is_true ((_p_E_equal e _p_E_perfect_match))).
    Variable abst_diag : (Datatypes.prod _p_V_T _p_P_T) -> _p_P_T.
    Variable abst_state : _p_P_T -> _p_E_T.
    Variable abst_voter : _p_V_T ->
                            _p_V_T ->
                              _p_V_T -> (Datatypes.prod _p_V_T _p_P_T).
(* File "vote.fcl", line 139, characters 10-34 *)
Theorem for_zenon_t1:(forall v1:_p_V_T,(forall v2:_p_V_T,(forall v3
:_p_V_T,((Is_true (_p_E_equal (abst_state (abst_diag (abst_voter v1 v2
v3))) _p_E_no_match))\/((Is_true (_p_E_equal (abst_state (abst_diag (
abst_voter v1 v2 v3))) _p_E_range_match))\/((Is_true (_p_E_equal (
abst_state (abst_diag (abst_voter v1 v2 v3))) _p_E_partial_match))\/(
Is_true (_p_E_equal (abst_state (abst_diag (abst_voter v1 v2 v3)))
_p_E_perfect_match)))))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun v1:_p_V_T=>(forall v2:_p_V_T,
(forall v3:_p_V_T,((Is_true (_p_E_equal (abst_state (abst_diag (
abst_voter v1 v2 v3))) _p_E_no_match))\/((Is_true (_p_E_equal (
abst_state (abst_diag (abst_voter v1 v2 v3))) _p_E_range_match))\/((
Is_true (_p_E_equal (abst_state (abst_diag (abst_voter v1 v2 v3)))
_p_E_partial_match))\/(Is_true (_p_E_equal (abst_state (abst_diag (
abst_voter v1 v2 v3))) _p_E_perfect_match)))))))) (fun zenon_Hb=>(
zenon_ex _p_V_T (fun v1:_p_V_T=>(~(forall v2:_p_V_T,(forall v3:_p_V_T,((
Is_true (_p_E_equal (abst_state (abst_diag (abst_voter v1 v2 v3)))
_p_E_no_match))\/((Is_true (_p_E_equal (abst_state (abst_diag (
abst_voter v1 v2 v3))) _p_E_range_match))\/((Is_true (_p_E_equal (
abst_state (abst_diag (abst_voter v1 v2 v3))) _p_E_partial_match))\/(
Is_true (_p_E_equal (abst_state (abst_diag (abst_voter v1 v2 v3)))
_p_E_perfect_match))))))))) (fun(zenon_Tv1_c:_p_V_T) zenon_Ha=>(
zenon_notallex (fun v2:_p_V_T=>(forall v3:_p_V_T,((Is_true (_p_E_equal (
abst_state (abst_diag (abst_voter zenon_Tv1_c v2 v3))) _p_E_no_match))
\/((Is_true (_p_E_equal (abst_state (abst_diag (abst_voter zenon_Tv1_c
v2 v3))) _p_E_range_match))\/((Is_true (_p_E_equal (abst_state (
abst_diag (abst_voter zenon_Tv1_c v2 v3))) _p_E_partial_match))\/(
Is_true (_p_E_equal (abst_state (abst_diag (abst_voter zenon_Tv1_c v2
v3))) _p_E_perfect_match))))))) (fun zenon_H9=>(zenon_ex _p_V_T (fun v2
:_p_V_T=>(~(forall v3:_p_V_T,((Is_true (_p_E_equal (abst_state (
abst_diag (abst_voter zenon_Tv1_c v2 v3))) _p_E_no_match))\/((Is_true (
_p_E_equal (abst_state (abst_diag (abst_voter zenon_Tv1_c v2 v3)))
_p_E_range_match))\/((Is_true (_p_E_equal (abst_state (abst_diag (
abst_voter zenon_Tv1_c v2 v3))) _p_E_partial_match))\/(Is_true (
_p_E_equal (abst_state (abst_diag (abst_voter zenon_Tv1_c v2 v3)))
_p_E_perfect_match)))))))) (fun(zenon_Tv2_d:_p_V_T) zenon_H8=>(
zenon_notallex (fun v3:_p_V_T=>((Is_true (_p_E_equal (abst_state (
abst_diag (abst_voter zenon_Tv1_c zenon_Tv2_d v3))) _p_E_no_match))\/((
Is_true (_p_E_equal (abst_state (abst_diag (abst_voter zenon_Tv1_c
zenon_Tv2_d v3))) _p_E_range_match))\/((Is_true (_p_E_equal (abst_state
(abst_diag (abst_voter zenon_Tv1_c zenon_Tv2_d v3))) _p_E_partial_match)
)\/(Is_true (_p_E_equal (abst_state (abst_diag (abst_voter zenon_Tv1_c
zenon_Tv2_d v3))) _p_E_perfect_match)))))) (fun zenon_H7=>(zenon_ex
_p_V_T (fun v3:_p_V_T=>(~((Is_true (_p_E_equal (abst_state (abst_diag (
abst_voter zenon_Tv1_c zenon_Tv2_d v3))) _p_E_no_match))\/((Is_true (
_p_E_equal (abst_state (abst_diag (abst_voter zenon_Tv1_c zenon_Tv2_d
v3))) _p_E_range_match))\/((Is_true (_p_E_equal (abst_state (abst_diag (
abst_voter zenon_Tv1_c zenon_Tv2_d v3))) _p_E_partial_match))\/(Is_true
(_p_E_equal (abst_state (abst_diag (abst_voter zenon_Tv1_c zenon_Tv2_d
v3))) _p_E_perfect_match))))))) (fun(zenon_Tv3_g:_p_V_T) zenon_H5=>(
zenon_all _p_E_T (fun e:_p_E_T=>((Is_true (_p_E_equal e _p_E_no_match))
\/((Is_true (_p_E_equal e _p_E_range_match))\/((Is_true (_p_E_equal e
_p_E_partial_match))\/(Is_true (_p_E_equal e _p_E_perfect_match)))))) (
abst_state (abst_diag (abst_voter zenon_Tv1_c zenon_Tv2_d zenon_Tv3_g)))
 (fun zenon_H4=>(zenon_H5 zenon_H4)) _p_E_all_value)) zenon_H7))
zenon_H8)) zenon_H9)) zenon_Ha)) zenon_Hb)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_t1 :
      forall v1  v2  v3 : _p_V_T,
        Is_true ((_p_E_equal (abst_state (abst_diag (abst_voter v1 v2 v3)))
                   _p_E_no_match)) \/
          Is_true ((_p_E_equal (abst_state (abst_diag (abst_voter v1 v2 v3)))
                     _p_E_range_match)) \/
            Is_true ((_p_E_equal
                       (abst_state (abst_diag (abst_voter v1 v2 v3)))
                       _p_E_partial_match)) \/
              Is_true ((_p_E_equal
                         (abst_state (abst_diag (abst_voter v1 v2 v3)))
                         _p_E_perfect_match)).
    assert (__force_use_p_E_T := _p_E_T).
    assert (__force_use_p_V_T := _p_V_T).
    assert (__force_use_p_P_T := _p_P_T).
    assert (__force_use__p_E_equal := _p_E_equal).
    assert (__force_use__p_E_no_match := _p_E_no_match).
    assert (__force_use__p_E_partial_match := _p_E_partial_match).
    assert (__force_use__p_E_perfect_match := _p_E_perfect_match).
    assert (__force_use__p_E_range_match := _p_E_range_match).
    assert (__force_use__p_E_all_value := _p_E_all_value).
    assert (__force_use_abst_diag := abst_diag).
    assert (__force_use_abst_state := abst_state).
    assert (__force_use_abst_voter := abst_voter).
    apply for_zenon_t1;
    auto.
    Qed.
    End Proof_of_t1.
  
  Theorem t1  (_p_E_T : Set) (_p_V_T : Set) (_p_P_T : Set) (_p_E_equal :
    _p_E_T -> _p_E_T -> basics.bool__t) (_p_E_no_match : _p_E_T)
    (_p_E_partial_match : _p_E_T) (_p_E_perfect_match : _p_E_T)
    (_p_E_range_match : _p_E_T) (_p_E_all_value :
    forall e : _p_E_T,
      (Is_true ((_p_E_equal e _p_E_no_match)) \/
         Is_true ((_p_E_equal e _p_E_range_match)) \/
           Is_true ((_p_E_equal e _p_E_partial_match)) \/
             Is_true ((_p_E_equal e _p_E_perfect_match))))
    (abst_diag : (Datatypes.prod _p_V_T _p_P_T) -> _p_P_T)
    (abst_state : _p_P_T -> _p_E_T)
    (abst_voter : _p_V_T ->
                    _p_V_T -> _p_V_T -> (Datatypes.prod _p_V_T _p_P_T)):
    forall v1  v2  v3 : _p_V_T,
      Is_true ((_p_E_equal (abst_state (abst_diag (abst_voter v1 v2 v3)))
                 _p_E_no_match)) \/
        Is_true ((_p_E_equal (abst_state (abst_diag (abst_voter v1 v2 v3)))
                   _p_E_range_match)) \/
          Is_true ((_p_E_equal (abst_state (abst_diag (abst_voter v1 v2 v3)))
                     _p_E_partial_match)) \/
            Is_true ((_p_E_equal
                       (abst_state (abst_diag (abst_voter v1 v2 v3)))
                       _p_E_perfect_match)).
  apply for_zenon_abstracted_t1;
  auto.
  Qed.
  
  (* From species vote#Voteur. *)
  (* Section for proof of theorem 't2'. *)
  Section Proof_of_t2.
    Variable _p_C_T : Set.
    Variable _p_V_T : Set.
    Variable _p_P_T : Set.
    Variable _p_C_capt_1 : _p_C_T.
    Variable _p_C_capt_2 : _p_C_T.
    Variable _p_C_capt_3 : _p_C_T.
    Variable _p_C_equal : _p_C_T -> _p_C_T -> basics.bool__t.
    Variable _p_C_all_value :
      forall e : _p_C_T,
        Is_true ((_p_C_equal e _p_C_capt_1)) \/
          Is_true ((_p_C_equal e _p_C_capt_2)) \/
            Is_true ((_p_C_equal e _p_C_capt_3)).
    Variable abst_diag : (Datatypes.prod _p_V_T _p_P_T) -> _p_P_T.
    Variable abst_sensor : _p_P_T -> _p_C_T.
    Variable abst_voter : _p_V_T ->
                            _p_V_T ->
                              _p_V_T -> (Datatypes.prod _p_V_T _p_P_T).
(* File "vote.fcl", line 146, characters 10-33 *)
Theorem for_zenon_t2:(forall v1:_p_V_T,(forall v2:_p_V_T,(forall v3
:_p_V_T,((Is_true (_p_C_equal (abst_sensor (abst_diag (abst_voter v1 v2
v3))) _p_C_capt_1))\/((Is_true (_p_C_equal (abst_sensor (abst_diag (
abst_voter v1 v2 v3))) _p_C_capt_2))\/(Is_true (_p_C_equal (abst_sensor
(abst_diag (abst_voter v1 v2 v3))) _p_C_capt_3))))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun v1:_p_V_T=>(forall v2:_p_V_T,
(forall v3:_p_V_T,((Is_true (_p_C_equal (abst_sensor (abst_diag (
abst_voter v1 v2 v3))) _p_C_capt_1))\/((Is_true (_p_C_equal (
abst_sensor (abst_diag (abst_voter v1 v2 v3))) _p_C_capt_2))\/(Is_true (
_p_C_equal (abst_sensor (abst_diag (abst_voter v1 v2 v3))) _p_C_capt_3))
))))) (fun zenon_Hb=>(zenon_ex _p_V_T (fun v1:_p_V_T=>(~(forall v2
:_p_V_T,(forall v3:_p_V_T,((Is_true (_p_C_equal (abst_sensor (abst_diag
(abst_voter v1 v2 v3))) _p_C_capt_1))\/((Is_true (_p_C_equal (
abst_sensor (abst_diag (abst_voter v1 v2 v3))) _p_C_capt_2))\/(Is_true (
_p_C_equal (abst_sensor (abst_diag (abst_voter v1 v2 v3))) _p_C_capt_3))
)))))) (fun(zenon_Tv1_c:_p_V_T) zenon_Ha=>(zenon_notallex (fun v2
:_p_V_T=>(forall v3:_p_V_T,((Is_true (_p_C_equal (abst_sensor (
abst_diag (abst_voter zenon_Tv1_c v2 v3))) _p_C_capt_1))\/((Is_true (
_p_C_equal (abst_sensor (abst_diag (abst_voter zenon_Tv1_c v2 v3)))
_p_C_capt_2))\/(Is_true (_p_C_equal (abst_sensor (abst_diag (abst_voter
zenon_Tv1_c v2 v3))) _p_C_capt_3)))))) (fun zenon_H9=>(zenon_ex _p_V_T (
fun v2:_p_V_T=>(~(forall v3:_p_V_T,((Is_true (_p_C_equal (abst_sensor (
abst_diag (abst_voter zenon_Tv1_c v2 v3))) _p_C_capt_1))\/((Is_true (
_p_C_equal (abst_sensor (abst_diag (abst_voter zenon_Tv1_c v2 v3)))
_p_C_capt_2))\/(Is_true (_p_C_equal (abst_sensor (abst_diag (abst_voter
zenon_Tv1_c v2 v3))) _p_C_capt_3))))))) (fun(zenon_Tv2_d:_p_V_T)
zenon_H8=>(zenon_notallex (fun v3:_p_V_T=>((Is_true (_p_C_equal (
abst_sensor (abst_diag (abst_voter zenon_Tv1_c zenon_Tv2_d v3)))
_p_C_capt_1))\/((Is_true (_p_C_equal (abst_sensor (abst_diag (
abst_voter zenon_Tv1_c zenon_Tv2_d v3))) _p_C_capt_2))\/(Is_true (
_p_C_equal (abst_sensor (abst_diag (abst_voter zenon_Tv1_c zenon_Tv2_d
v3))) _p_C_capt_3))))) (fun zenon_H7=>(zenon_ex _p_V_T (fun v3:_p_V_T=>(
~((Is_true (_p_C_equal (abst_sensor (abst_diag (abst_voter zenon_Tv1_c
zenon_Tv2_d v3))) _p_C_capt_1))\/((Is_true (_p_C_equal (abst_sensor (
abst_diag (abst_voter zenon_Tv1_c zenon_Tv2_d v3))) _p_C_capt_2))\/(
Is_true (_p_C_equal (abst_sensor (abst_diag (abst_voter zenon_Tv1_c
zenon_Tv2_d v3))) _p_C_capt_3)))))) (fun(zenon_Tv3_g:_p_V_T) zenon_H5=>(
zenon_all _p_C_T (fun e:_p_C_T=>((Is_true (_p_C_equal e _p_C_capt_1))\/(
(Is_true (_p_C_equal e _p_C_capt_2))\/(Is_true (_p_C_equal e
_p_C_capt_3))))) (abst_sensor (abst_diag (abst_voter zenon_Tv1_c
zenon_Tv2_d zenon_Tv3_g))) (fun zenon_H4=>(zenon_H5 zenon_H4))
_p_C_all_value)) zenon_H7)) zenon_H8)) zenon_H9)) zenon_Ha)) zenon_Hb))
zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_t2 :
      forall v1  v2  v3 : _p_V_T,
        Is_true ((_p_C_equal (abst_sensor (abst_diag (abst_voter v1 v2 v3)))
                   _p_C_capt_1)) \/
          Is_true ((_p_C_equal
                     (abst_sensor (abst_diag (abst_voter v1 v2 v3)))
                     _p_C_capt_2)) \/
            Is_true ((_p_C_equal
                       (abst_sensor (abst_diag (abst_voter v1 v2 v3)))
                       _p_C_capt_3)).
    assert (__force_use_p_C_T := _p_C_T).
    assert (__force_use_p_V_T := _p_V_T).
    assert (__force_use_p_P_T := _p_P_T).
    assert (__force_use__p_C_capt_1 := _p_C_capt_1).
    assert (__force_use__p_C_capt_2 := _p_C_capt_2).
    assert (__force_use__p_C_capt_3 := _p_C_capt_3).
    assert (__force_use__p_C_equal := _p_C_equal).
    assert (__force_use__p_C_all_value := _p_C_all_value).
    assert (__force_use_abst_diag := abst_diag).
    assert (__force_use_abst_sensor := abst_sensor).
    assert (__force_use_abst_voter := abst_voter).
    apply for_zenon_t2;
    auto.
    Qed.
    End Proof_of_t2.
  
  Theorem t2  (_p_C_T : Set) (_p_V_T : Set) (_p_P_T : Set) (_p_C_capt_1 :
    _p_C_T) (_p_C_capt_2 : _p_C_T) (_p_C_capt_3 : _p_C_T) (_p_C_equal :
    _p_C_T -> _p_C_T -> basics.bool__t) (_p_C_all_value :
    forall e : _p_C_T,
      Is_true ((_p_C_equal e _p_C_capt_1)) \/
        Is_true ((_p_C_equal e _p_C_capt_2)) \/
          Is_true ((_p_C_equal e _p_C_capt_3)))
    (abst_diag : (Datatypes.prod _p_V_T _p_P_T) -> _p_P_T)
    (abst_sensor : _p_P_T -> _p_C_T)
    (abst_voter : _p_V_T ->
                    _p_V_T -> _p_V_T -> (Datatypes.prod _p_V_T _p_P_T)):
    forall v1  v2  v3 : _p_V_T,
      Is_true ((_p_C_equal (abst_sensor (abst_diag (abst_voter v1 v2 v3)))
                 _p_C_capt_1)) \/
        Is_true ((_p_C_equal (abst_sensor (abst_diag (abst_voter v1 v2 v3)))
                   _p_C_capt_2)) \/
          Is_true ((_p_C_equal
                     (abst_sensor (abst_diag (abst_voter v1 v2 v3)))
                     _p_C_capt_3)).
  apply for_zenon_abstracted_t2;
  auto.
  Qed.
  
  (* From species vote#Voteur. *)
  (* Section for proof of theorem 'voter_independant_from_order_v1_v2'. *)
  Section Proof_of_voter_independant_from_order_v1_v2.
    Variable _p_E_T : Set.
    Variable _p_C_T : Set.
    Variable _p_V_T : Set.
    Variable _p_P_T : Set.
    Variable _p_E_equal : _p_E_T -> _p_E_T -> basics.bool__t.
    Variable _p_E_no_match : _p_E_T.
    Variable _p_E_partial_match : _p_E_T.
    Variable _p_E_perfect_match : _p_E_T.
    Variable _p_E_range_match : _p_E_T.
    Variable _p_C_capt_1 : _p_C_T.
    Variable _p_C_capt_2 : _p_C_T.
    Variable _p_C_capt_3 : _p_C_T.
    Variable _p_V_consistency_rule : _p_V_T -> _p_V_T -> basics.bool__t.
    Variable _p_V_consistency_rule_reflexive :
      forall a : _p_V_T, Is_true ((_p_V_consistency_rule a a)).
    Variable _p_V_consistency_rule_symmetric :
      forall a  b : _p_V_T,
        Is_true ((_p_V_consistency_rule a b)) ->
          Is_true ((_p_V_consistency_rule b a)).
    Variable _p_P_constr : _p_C_T -> _p_E_T -> _p_P_T.
    Variable _p_P_prj_b : _p_P_T -> _p_E_T.
    Variable _p_P_valid : _p_P_T -> basics.bool__t.
    Variable _p_P_prj_b_is_snd_of_pair :
      forall n1 : _p_C_T,
        forall n2 : _p_E_T,
          Is_true ((_p_E_equal (_p_P_prj_b (_p_P_constr n1 n2)) n2)).
    Variable _p_P_no_match_is_invalid :
      forall x : _p_P_T,
        Is_true ((_p_E_equal (_p_P_prj_b x) _p_E_no_match)) ->
          ~Is_true (((_p_P_valid x))).
    Variable _p_P_partial_match_is_valid :
      forall x : _p_P_T,
        Is_true ((_p_E_equal (_p_P_prj_b x) _p_E_partial_match)) ->
          Is_true ((_p_P_valid x)).
    Variable _p_P_perfect_match_is_valid :
      forall x : _p_P_T,
        Is_true ((_p_E_equal (_p_P_prj_b x) _p_E_perfect_match)) ->
          Is_true ((_p_P_valid x)).
    Variable _p_P_range_match_is_valid :
      forall x : _p_P_T,
        Is_true ((_p_E_equal (_p_P_prj_b x) _p_E_range_match)) ->
          Is_true ((_p_P_valid x)).
    Hypothesis abst_consistency_rule_is_symmetric :
      forall v1  v2 : _p_V_T,
        Is_true ((_p_V_consistency_rule v1 v2)) ->
          Is_true ((_p_V_consistency_rule v2 v1)).
    Variable abst_diag : (Datatypes.prod _p_V_T _p_P_T) -> _p_P_T.
    Variable abst_value : (Datatypes.prod _p_V_T _p_P_T) -> _p_V_T.
    Variable abst_voter : _p_V_T ->
                            _p_V_T ->
                              _p_V_T -> (Datatypes.prod _p_V_T _p_P_T).
    Let abst_compatible := gen_vote.Gen_voter.compatible _p_V_T _p_P_T
    _p_V_consistency_rule _p_P_valid abst_diag
    abst_value.
    Hypothesis abst_vote_match_c1 :
      forall v1  v2  v3 : _p_V_T,
        (~Is_true ((_p_V_consistency_rule v1 v2)) /\
           ~Is_true ((_p_V_consistency_rule v1 v3)) /\
             Is_true ((_p_V_consistency_rule v2 v3))) ->
          (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                       v2))) /\
             Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                         (_p_P_constr _p_C_capt_1 _p_E_range_match))))).
    Hypothesis abst_vote_match_c2 :
      forall v1  v2  v3 : _p_V_T,
        (~Is_true ((_p_V_consistency_rule v1 v2)) /\
           Is_true ((_p_V_consistency_rule v1 v3)) /\
             ~Is_true ((_p_V_consistency_rule v2 v3))) ->
          (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                       v3))) /\
             Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                         (_p_P_constr _p_C_capt_2 _p_E_range_match))))).
    Hypothesis abst_vote_match_c3 :
      forall v1  v2  v3 : _p_V_T,
        (Is_true ((_p_V_consistency_rule v1 v2)) /\
           ~Is_true ((_p_V_consistency_rule v1 v3)) /\
             ~Is_true ((_p_V_consistency_rule v2 v3))) ->
          (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                       v1))) /\
             Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                         (_p_P_constr _p_C_capt_3 _p_E_range_match))))).
    Hypothesis abst_vote_no_match :
      forall v1  v2  v3 : _p_V_T,
        (~Is_true ((_p_V_consistency_rule v1 v2)) /\
           ~Is_true ((_p_V_consistency_rule v1 v3)) /\
             ~Is_true ((_p_V_consistency_rule v2 v3))) ->
          Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                      (_p_P_constr _p_C_capt_1 _p_E_no_match)))).
    Hypothesis abst_vote_partial_c1 :
      forall v1  v2  v3 : _p_V_T,
        (Is_true ((_p_V_consistency_rule v1 v2)) /\
           Is_true ((_p_V_consistency_rule v1 v3)) /\
             ~Is_true ((_p_V_consistency_rule v2 v3))) ->
          (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                       v1))) /\
             Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                         (_p_P_constr _p_C_capt_1 _p_E_partial_match))))).
    Hypothesis abst_vote_partial_c2 :
      forall v1  v2  v3 : _p_V_T,
        (Is_true ((_p_V_consistency_rule v1 v2)) /\
           ~Is_true ((_p_V_consistency_rule v1 v3)) /\
             Is_true ((_p_V_consistency_rule v2 v3))) ->
          (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                       v2))) /\
             Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                         (_p_P_constr _p_C_capt_2 _p_E_partial_match))))).
    Hypothesis abst_vote_partial_c3 :
      forall v1  v2  v3 : _p_V_T,
        (~Is_true ((_p_V_consistency_rule v1 v2)) /\
           Is_true ((_p_V_consistency_rule v1 v3)) /\
             Is_true ((_p_V_consistency_rule v2 v3))) ->
          (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                       v3))) /\
             Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                         (_p_P_constr _p_C_capt_3 _p_E_partial_match))))).
    Hypothesis abst_vote_perfect :
      forall v1  v2  v3 : _p_V_T,
        (Is_true ((_p_V_consistency_rule v1 v2)) /\
           Is_true ((_p_V_consistency_rule v2 v3)) /\
             Is_true ((_p_V_consistency_rule v1 v3))) ->
          (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                       v1))) /\
             Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                         (_p_P_constr _p_C_capt_1 _p_E_perfect_match))))).
    Section __C_1.
      Variable va : _p_V_T.
      Variable vb : _p_V_T.
      Variable vc : _p_V_T.
      Section __C_1_1.
        Variable H1 : Is_true ((_p_V_consistency_rule va vb)).
        Section __C_1_1_1.
          Variable H11 : Is_true ((_p_V_consistency_rule va vc)).
          Section __C_1_1_1_1.
            Variable H111 : Is_true ((_p_V_consistency_rule vb vc)).
            Section __C_1_1_1_1_1.
(* File "vote.fcl", line 299, character 10, line 300, character 34 *)
Theorem for_zenon___C_1_1_1_1_1_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) va)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((
Is_true (_p_V_consistency_rule v2 v3))/\(Is_true (_p_V_consistency_rule
v1 v3))))->((Is_true (basics._equal_ _ (abst_value (abst_voter v1 v2 v3)
) v1))/\(Is_true (basics._equal_ _ (abst_diag (abst_voter v1 v2 v3)) (
_p_P_constr _p_C_capt_1 _p_E_perfect_match)))))))) va (fun zenon_Hf=>(
zenon_all _p_V_T (fun v2:_p_V_T=>(forall v3:_p_V_T,(((Is_true (
_p_V_consistency_rule va v2))/\((Is_true (_p_V_consistency_rule v2 v3))
/\(Is_true (_p_V_consistency_rule va v3))))->((Is_true (basics._equal_
_ (abst_value (abst_voter va v2 v3)) va))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_perfect_match))))))) vb (fun zenon_He=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule va vb))/\((Is_true (
_p_V_consistency_rule vb v3))/\(Is_true (_p_V_consistency_rule va v3))))
->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) va))/\(
Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_1 _p_E_perfect_match)))))) vc (fun zenon_Hd=>(
zenon_imply _ _ (fun zenon_Hc=>(zenon_notand _ _ (fun zenon_Hb=>(
zenon_Hb H1)) (fun zenon_Ha=>(zenon_notand _ _ (fun zenon_H9=>(zenon_H9
H111)) (fun zenon_H8=>(zenon_H8 H11)) zenon_Ha)) zenon_Hc)) (fun
zenon_H7=>(zenon_and _ _ (fun zenon_H5 zenon_H6=>(zenon_G zenon_H5))
zenon_H7)) zenon_Hd)) zenon_He)) zenon_Hf)) abst_vote_perfect)))).
Qed.

              Theorem __C_1_1_1_1_1_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter va vb vc)) va))).
              assert (__force_use_H111 := H111).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_1_1_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_1_1.
            Section __C_1_1_1_1_2.
(* File "vote.fcl", line 302, character 10, line 303, character 65 *)
Theorem for_zenon___C_1_1_1_1_2_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter vb va vc)) vb)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((
Is_true (_p_V_consistency_rule v2 v3))/\(Is_true (_p_V_consistency_rule
v1 v3))))->((Is_true (basics._equal_ _ (abst_value (abst_voter v1 v2 v3)
) v1))/\(Is_true (basics._equal_ _ (abst_diag (abst_voter v1 v2 v3)) (
_p_P_constr _p_C_capt_1 _p_E_perfect_match)))))))) vb (fun zenon_H14=>(
zenon_all _p_V_T (fun v2:_p_V_T=>(forall v3:_p_V_T,(((Is_true (
_p_V_consistency_rule vb v2))/\((Is_true (_p_V_consistency_rule v2 v3))
/\(Is_true (_p_V_consistency_rule vb v3))))->((Is_true (basics._equal_
_ (abst_value (abst_voter vb v2 v3)) vb))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_perfect_match))))))) va (fun zenon_H13=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule vb va))/\((Is_true (
_p_V_consistency_rule va v3))/\(Is_true (_p_V_consistency_rule vb v3))))
->((Is_true (basics._equal_ _ (abst_value (abst_voter vb va v3)) vb))/\(
Is_true (basics._equal_ _ (abst_diag (abst_voter vb va v3)) (
_p_P_constr _p_C_capt_1 _p_E_perfect_match)))))) vc (fun zenon_H12=>(
zenon_imply _ _ (fun zenon_H11=>(zenon_notand _ _ (fun zenon_Hd=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) va (fun zenon_H10=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule va v2))->(Is_true (_p_V_consistency_rule v2 va))))
 vb (fun zenon_Hf=>(zenon_imply _ _ (fun zenon_He=>(zenon_He H1)) (fun
zenon_Hc=>(zenon_Hd zenon_Hc)) zenon_Hf)) zenon_H10))
abst_consistency_rule_is_symmetric)) (fun zenon_Hb=>(zenon_notand _ _ (
fun zenon_Ha=>(zenon_Ha H11)) (fun zenon_H9=>(zenon_H9 H111)) zenon_Hb))
 zenon_H11)) (fun zenon_H8=>(zenon_and _ _ (fun zenon_H6 zenon_H7=>(
zenon_G zenon_H6)) zenon_H8)) zenon_H12)) zenon_H13)) zenon_H14))
abst_vote_perfect)))).
Qed.

              Theorem __C_1_1_1_1_2_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter vb va vc)) vb))).
              assert (__force_use_H111 := H111).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_1_2_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_1_2.
            Section __C_1_1_1_1_3.
(* File "vote.fcl", line 305, character 10, line 306, character 65 *)
Theorem for_zenon___C_1_1_1_1_3_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter vc va vb)) vc)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((
Is_true (_p_V_consistency_rule v2 v3))/\(Is_true (_p_V_consistency_rule
v1 v3))))->((Is_true (basics._equal_ _ (abst_value (abst_voter v1 v2 v3)
) v1))/\(Is_true (basics._equal_ _ (abst_diag (abst_voter v1 v2 v3)) (
_p_P_constr _p_C_capt_1 _p_E_perfect_match)))))))) vc (fun zenon_H18=>(
zenon_all _p_V_T (fun v2:_p_V_T=>(forall v3:_p_V_T,(((Is_true (
_p_V_consistency_rule vc v2))/\((Is_true (_p_V_consistency_rule v2 v3))
/\(Is_true (_p_V_consistency_rule vc v3))))->((Is_true (basics._equal_
_ (abst_value (abst_voter vc v2 v3)) vc))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_perfect_match))))))) va (fun zenon_H17=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule vc va))/\((Is_true (
_p_V_consistency_rule va v3))/\(Is_true (_p_V_consistency_rule vc v3))))
->((Is_true (basics._equal_ _ (abst_value (abst_voter vc va v3)) vc))/\(
Is_true (basics._equal_ _ (abst_diag (abst_voter vc va v3)) (
_p_P_constr _p_C_capt_1 _p_E_perfect_match)))))) vb (fun zenon_H16=>(
zenon_imply _ _ (fun zenon_H15=>(zenon_notand _ _ (fun zenon_H11=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) va (fun zenon_H14=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule va v2))->(Is_true (_p_V_consistency_rule v2 va))))
 vc (fun zenon_H13=>(zenon_imply _ _ (fun zenon_H12=>(zenon_H12 H11)) (
fun zenon_H10=>(zenon_H11 zenon_H10)) zenon_H13)) zenon_H14))
abst_consistency_rule_is_symmetric)) (fun zenon_Hf=>(zenon_notand _ _ (
fun zenon_He=>(zenon_He H1)) (fun zenon_Ha=>(zenon_all _p_V_T (fun v1
:_p_V_T=>(forall v2:_p_V_T,((Is_true (_p_V_consistency_rule v1 v2))->(
Is_true (_p_V_consistency_rule v2 v1))))) vb (fun zenon_Hd=>(zenon_all
_p_V_T (fun v2:_p_V_T=>((Is_true (_p_V_consistency_rule vb v2))->(
Is_true (_p_V_consistency_rule v2 vb)))) vc (fun zenon_Hc=>(zenon_imply
_ _ (fun zenon_Hb=>(zenon_Hb H111)) (fun zenon_H9=>(zenon_Ha zenon_H9))
zenon_Hc)) zenon_Hd)) abst_consistency_rule_is_symmetric)) zenon_Hf))
zenon_H15)) (fun zenon_H8=>(zenon_and _ _ (fun zenon_H6 zenon_H7=>(
zenon_G zenon_H6)) zenon_H8)) zenon_H16)) zenon_H17)) zenon_H18))
abst_vote_perfect)))).
Qed.

              Theorem __C_1_1_1_1_3_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter vc va vb)) vc))).
              assert (__force_use_H111 := H111).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_1_3_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_1_3.
            Section __C_1_1_1_1_4.
(* File "vote.fcl", line 310, characters 10-59 *)
Theorem for_zenon___C_1_1_1_1_4_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter va vb vc)) (_p_P_constr _p_C_capt_1
_p_E_perfect_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((
Is_true (_p_V_consistency_rule v2 v3))/\(Is_true (_p_V_consistency_rule
v1 v3))))->((Is_true (basics._equal_ _ (abst_value (abst_voter v1 v2 v3)
) v1))/\(Is_true (basics._equal_ _ (abst_diag (abst_voter v1 v2 v3)) (
_p_P_constr _p_C_capt_1 _p_E_perfect_match)))))))) va (fun zenon_Hf=>(
zenon_all _p_V_T (fun v2:_p_V_T=>(forall v3:_p_V_T,(((Is_true (
_p_V_consistency_rule va v2))/\((Is_true (_p_V_consistency_rule v2 v3))
/\(Is_true (_p_V_consistency_rule va v3))))->((Is_true (basics._equal_
_ (abst_value (abst_voter va v2 v3)) va))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_perfect_match))))))) vb (fun zenon_He=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule va vb))/\((Is_true (
_p_V_consistency_rule vb v3))/\(Is_true (_p_V_consistency_rule va v3))))
->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) va))/\(
Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_1 _p_E_perfect_match)))))) vc (fun zenon_Hd=>(
zenon_imply _ _ (fun zenon_Hc=>(zenon_notand _ _ (fun zenon_Hb=>(
zenon_Hb H1)) (fun zenon_Ha=>(zenon_notand _ _ (fun zenon_H9=>(zenon_H9
H111)) (fun zenon_H8=>(zenon_H8 H11)) zenon_Ha)) zenon_Hc)) (fun
zenon_H7=>(zenon_and _ _ (fun zenon_H6 zenon_H5=>(zenon_G zenon_H5))
zenon_H7)) zenon_Hd)) zenon_He)) zenon_Hf)) abst_vote_perfect)))).
Qed.

              Theorem __C_1_1_1_1_4_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter va vb vc))
                            (_p_P_constr _p_C_capt_1 _p_E_perfect_match)))).
              assert (__force_use_H111 := H111).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_1_4_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_1_4.
            Section __C_1_1_1_1_5.
(* File "vote.fcl", line 312, characters 10-80 *)
Theorem for_zenon___C_1_1_1_1_5_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter va vb vc)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter va vb vc)) (_p_P_constr
_p_C_capt_1 _p_E_perfect_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_perfect_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter va vb vc)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_1 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 n2)) n2))) _p_E_perfect_match (fun zenon_H6=>(zenon_subst _
(fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 _p_E_perfect_match)) _p_E_perfect_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter va vb vc))) _p_E_perfect_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_perfect_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter va
vb vc))) _p_E_perfect_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_1
_p_E_perfect_match)) (_p_P_prj_b (abst_diag (abst_voter va vb vc))) (
fun zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter va vb vc)))))) (_p_P_constr
_p_C_capt_1 _p_E_perfect_match) (abst_diag (abst_voter va vb vc)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter va vb vc)) (_p_P_constr
_p_C_capt_1 _p_E_perfect_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter va vb vc))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter va vb vc))) _p_E_perfect_match))) zenon_H7)) zenon_H5
zenon_H6)) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(
zenon_G zenon_H4)) zenon_Hc)) _p_P_perfect_match_is_valid))
__C_1_1_1_1_4_LEMMA)))).
Qed.

              Theorem __C_1_1_1_1_5_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter va vb vc))))).
              assert (__force_use_H111 := H111).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_1_5_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_1_5.
            Section __C_1_1_1_1_6.
(* File "vote.fcl", line 316, character 10, line 317, character 62 *)
Theorem for_zenon___C_1_1_1_1_6_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb va vc)) (_p_P_constr _p_C_capt_1
_p_E_perfect_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((
Is_true (_p_V_consistency_rule v2 v3))/\(Is_true (_p_V_consistency_rule
v1 v3))))->((Is_true (basics._equal_ _ (abst_value (abst_voter v1 v2 v3)
) v1))/\(Is_true (basics._equal_ _ (abst_diag (abst_voter v1 v2 v3)) (
_p_P_constr _p_C_capt_1 _p_E_perfect_match)))))))) vb (fun zenon_H14=>(
zenon_all _p_V_T (fun v2:_p_V_T=>(forall v3:_p_V_T,(((Is_true (
_p_V_consistency_rule vb v2))/\((Is_true (_p_V_consistency_rule v2 v3))
/\(Is_true (_p_V_consistency_rule vb v3))))->((Is_true (basics._equal_
_ (abst_value (abst_voter vb v2 v3)) vb))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_perfect_match))))))) va (fun zenon_H13=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule vb va))/\((Is_true (
_p_V_consistency_rule va v3))/\(Is_true (_p_V_consistency_rule vb v3))))
->((Is_true (basics._equal_ _ (abst_value (abst_voter vb va v3)) vb))/\(
Is_true (basics._equal_ _ (abst_diag (abst_voter vb va v3)) (
_p_P_constr _p_C_capt_1 _p_E_perfect_match)))))) vc (fun zenon_H12=>(
zenon_imply _ _ (fun zenon_H11=>(zenon_notand _ _ (fun zenon_Hd=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) va (fun zenon_H10=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule va v2))->(Is_true (_p_V_consistency_rule v2 va))))
 vb (fun zenon_Hf=>(zenon_imply _ _ (fun zenon_He=>(zenon_He H1)) (fun
zenon_Hc=>(zenon_Hd zenon_Hc)) zenon_Hf)) zenon_H10))
abst_consistency_rule_is_symmetric)) (fun zenon_Hb=>(zenon_notand _ _ (
fun zenon_Ha=>(zenon_Ha H11)) (fun zenon_H9=>(zenon_H9 H111)) zenon_Hb))
 zenon_H11)) (fun zenon_H8=>(zenon_and _ _ (fun zenon_H7 zenon_H6=>(
zenon_G zenon_H6)) zenon_H8)) zenon_H12)) zenon_H13)) zenon_H14))
abst_vote_perfect)))).
Qed.

              Theorem __C_1_1_1_1_6_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter vb va vc))
                            (_p_P_constr _p_C_capt_1 _p_E_perfect_match)))).
              assert (__force_use_H111 := H111).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_1_6_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_1_6.
            Section __C_1_1_1_1_7.
(* File "vote.fcl", line 319, characters 10-80 *)
Theorem for_zenon___C_1_1_1_1_7_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter vb va vc)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter vb va vc)) (_p_P_constr
_p_C_capt_1 _p_E_perfect_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_perfect_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter vb va vc)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_1 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 n2)) n2))) _p_E_perfect_match (fun zenon_H6=>(zenon_subst _
(fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 _p_E_perfect_match)) _p_E_perfect_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter vb va vc))) _p_E_perfect_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_perfect_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vb
va vc))) _p_E_perfect_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_1
_p_E_perfect_match)) (_p_P_prj_b (abst_diag (abst_voter vb va vc))) (
fun zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter vb va vc)))))) (_p_P_constr
_p_C_capt_1 _p_E_perfect_match) (abst_diag (abst_voter vb va vc)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter vb va vc)) (_p_P_constr
_p_C_capt_1 _p_E_perfect_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter vb va vc))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter vb va vc))) _p_E_perfect_match))) zenon_H7)) zenon_H5
zenon_H6)) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(
zenon_G zenon_H4)) zenon_Hc)) _p_P_perfect_match_is_valid))
__C_1_1_1_1_6_LEMMA)))).
Qed.

              Theorem __C_1_1_1_1_7_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter vb va vc))))).
              assert (__force_use_H111 := H111).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_1_7_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_1_7.
            Section __C_1_1_1_1_8.
(* File "vote.fcl", line 323, character 10, line 324, character 62 *)
Theorem for_zenon___C_1_1_1_1_8_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc va vb)) (_p_P_constr _p_C_capt_1
_p_E_perfect_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((
Is_true (_p_V_consistency_rule v2 v3))/\(Is_true (_p_V_consistency_rule
v1 v3))))->((Is_true (basics._equal_ _ (abst_value (abst_voter v1 v2 v3)
) v1))/\(Is_true (basics._equal_ _ (abst_diag (abst_voter v1 v2 v3)) (
_p_P_constr _p_C_capt_1 _p_E_perfect_match)))))))) vc (fun zenon_H18=>(
zenon_all _p_V_T (fun v2:_p_V_T=>(forall v3:_p_V_T,(((Is_true (
_p_V_consistency_rule vc v2))/\((Is_true (_p_V_consistency_rule v2 v3))
/\(Is_true (_p_V_consistency_rule vc v3))))->((Is_true (basics._equal_
_ (abst_value (abst_voter vc v2 v3)) vc))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_perfect_match))))))) va (fun zenon_H17=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule vc va))/\((Is_true (
_p_V_consistency_rule va v3))/\(Is_true (_p_V_consistency_rule vc v3))))
->((Is_true (basics._equal_ _ (abst_value (abst_voter vc va v3)) vc))/\(
Is_true (basics._equal_ _ (abst_diag (abst_voter vc va v3)) (
_p_P_constr _p_C_capt_1 _p_E_perfect_match)))))) vb (fun zenon_H16=>(
zenon_imply _ _ (fun zenon_H15=>(zenon_notand _ _ (fun zenon_H11=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) va (fun zenon_H14=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule va v2))->(Is_true (_p_V_consistency_rule v2 va))))
 vc (fun zenon_H13=>(zenon_imply _ _ (fun zenon_H12=>(zenon_H12 H11)) (
fun zenon_H10=>(zenon_H11 zenon_H10)) zenon_H13)) zenon_H14))
abst_consistency_rule_is_symmetric)) (fun zenon_Hf=>(zenon_notand _ _ (
fun zenon_He=>(zenon_He H1)) (fun zenon_Ha=>(zenon_all _p_V_T (fun v1
:_p_V_T=>(forall v2:_p_V_T,((Is_true (_p_V_consistency_rule v1 v2))->(
Is_true (_p_V_consistency_rule v2 v1))))) vb (fun zenon_Hd=>(zenon_all
_p_V_T (fun v2:_p_V_T=>((Is_true (_p_V_consistency_rule vb v2))->(
Is_true (_p_V_consistency_rule v2 vb)))) vc (fun zenon_Hc=>(zenon_imply
_ _ (fun zenon_Hb=>(zenon_Hb H111)) (fun zenon_H9=>(zenon_Ha zenon_H9))
zenon_Hc)) zenon_Hd)) abst_consistency_rule_is_symmetric)) zenon_Hf))
zenon_H15)) (fun zenon_H8=>(zenon_and _ _ (fun zenon_H7 zenon_H6=>(
zenon_G zenon_H6)) zenon_H8)) zenon_H16)) zenon_H17)) zenon_H18))
abst_vote_perfect)))).
Qed.

              Theorem __C_1_1_1_1_8_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter vc va vb))
                            (_p_P_constr _p_C_capt_1 _p_E_perfect_match)))).
              assert (__force_use_H111 := H111).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_1_8_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_1_8.
            Section __C_1_1_1_1_9.
(* File "vote.fcl", line 326, characters 10-80 *)
Theorem for_zenon___C_1_1_1_1_9_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter vc va vb)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter vc va vb)) (_p_P_constr
_p_C_capt_1 _p_E_perfect_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_perfect_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter vc va vb)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_1 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 n2)) n2))) _p_E_perfect_match (fun zenon_H6=>(zenon_subst _
(fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 _p_E_perfect_match)) _p_E_perfect_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter vc va vb))) _p_E_perfect_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_perfect_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vc
va vb))) _p_E_perfect_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_1
_p_E_perfect_match)) (_p_P_prj_b (abst_diag (abst_voter vc va vb))) (
fun zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter vc va vb)))))) (_p_P_constr
_p_C_capt_1 _p_E_perfect_match) (abst_diag (abst_voter vc va vb)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter vc va vb)) (_p_P_constr
_p_C_capt_1 _p_E_perfect_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter vc va vb))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter vc va vb))) _p_E_perfect_match))) zenon_H7)) zenon_H5
zenon_H6)) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(
zenon_G zenon_H4)) zenon_Hc)) _p_P_perfect_match_is_valid))
__C_1_1_1_1_8_LEMMA)))).
Qed.

              Theorem __C_1_1_1_1_9_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter vc va vb))))).
              assert (__force_use_H111 := H111).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_1_9_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_1_9.
(* File "vote.fcl", line 329, character 14, line 331, character 35 *)
Theorem for_zenon___C_1_1_1_1_LEMMA:((abst_compatible (abst_voter va vb
vc) (abst_voter vb va vc))/\(abst_compatible (abst_voter va vb vc) (
abst_voter vc va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notand _ _ (fun zenon_H1f=>(let zenon_H1e
:=zenon_H1f in (zenon_notor _ _ (fun zenon_H1c zenon_H1d=>(zenon_notand
_ _ (fun zenon_H11=>(zenon_H11 __C_1_1_1_1_5_LEMMA)) (fun zenon_H1b=>(
zenon_notand _ _ (fun zenon_H1a=>(zenon_H1a __C_1_1_1_1_7_LEMMA)) (fun
zenon_H16=>(coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (
abst_value (abst_voter va vb vc)) va (fun zenon_Hd=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (abst_value (
abst_voter vb va vc)) vb (fun zenon_H18=>(zenon_subst _ (fun zenon_Vi=>(
Is_true zenon_Vi)) (_p_V_consistency_rule va vb) (_p_V_consistency_rule
(abst_value (abst_voter va vb vc)) (abst_value (abst_voter vb va vc))) (
fun zenon_H17=>(zenon_subst _ (fun zenon_Vk=>(~((_p_V_consistency_rule
zenon_Vk vb) = (_p_V_consistency_rule (abst_value (abst_voter va vb vc))
 (abst_value (abst_voter vb va vc)))))) va (abst_value (abst_voter va
vb vc)) (fun zenon_He=>(zenon_eqsym _ (abst_value (abst_voter va vb vc))
 va zenon_Hd zenon_He)) (zenon_subst _ (fun zenon_Vj=>(~((
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) zenon_Vj) = (
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vb va vc)))))) vb (abst_value (abst_voter vb va vc)) (fun
zenon_H19=>(zenon_eqsym _ (abst_value (abst_voter vb va vc)) vb
zenon_H18 zenon_H19)) (zenon_notnot _ (refl_equal (
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vb va vc)))))) zenon_H17)) zenon_H16 H1))
__C_1_1_1_1_2_LEMMA)) __C_1_1_1_1_1_LEMMA)) zenon_H1b)) zenon_H1c))
zenon_H1e))) (fun zenon_H15=>(let zenon_H14:=zenon_H15 in (zenon_notor
_ _ (fun zenon_H12 zenon_H13=>(zenon_notand _ _ (fun zenon_H11=>(
zenon_H11 __C_1_1_1_1_5_LEMMA)) (fun zenon_H10=>(zenon_notand _ _ (fun
zenon_Hf=>(zenon_Hf __C_1_1_1_1_9_LEMMA)) (fun zenon_H9=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (abst_value (
abst_voter va vb vc)) va (fun zenon_Hd=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (abst_value (
abst_voter vc va vb)) vc (fun zenon_Hb=>(zenon_subst _ (fun zenon_Vf=>(
Is_true zenon_Vf)) (_p_V_consistency_rule va vc) (_p_V_consistency_rule
(abst_value (abst_voter va vb vc)) (abst_value (abst_voter vc va vb))) (
fun zenon_Ha=>(zenon_subst _ (fun zenon_Vh=>(~((_p_V_consistency_rule
zenon_Vh vc) = (_p_V_consistency_rule (abst_value (abst_voter va vb vc))
 (abst_value (abst_voter vc va vb)))))) va (abst_value (abst_voter va
vb vc)) (fun zenon_He=>(zenon_eqsym _ (abst_value (abst_voter va vb vc))
 va zenon_Hd zenon_He)) (zenon_subst _ (fun zenon_Vg=>(~((
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) zenon_Vg) = (
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vc va vb)))))) vc (abst_value (abst_voter vc va vb)) (fun
zenon_Hc=>(zenon_eqsym _ (abst_value (abst_voter vc va vb)) vc zenon_Hb
zenon_Hc)) (zenon_notnot _ (refl_equal (_p_V_consistency_rule (
abst_value (abst_voter va vb vc)) (abst_value (abst_voter vc va vb))))))
 zenon_Ha)) zenon_H9 H11)) __C_1_1_1_1_3_LEMMA)) __C_1_1_1_1_1_LEMMA))
zenon_H10)) zenon_H12)) zenon_H14))) zenon_G)))).
Qed.

            Theorem __C_1_1_1_1_LEMMA :
              ((abst_compatible (abst_voter va vb vc) (abst_voter vb va vc)) /\
                 (abst_compatible (abst_voter va vb vc)
                   (abst_voter vc va vb))).
            assert (__force_use_H111 := H111).
            assert (__force_use_H11 := H11).
            assert (__force_use_H1 := H1).
            apply for_zenon___C_1_1_1_1_LEMMA;
            auto.
            Qed.
            End __C_1_1_1_1.
          Section __C_1_1_1_2.
            Variable H112 : ~Is_true (((_p_V_consistency_rule vb vc))).
            Section __C_1_1_1_2_1.
(* File "vote.fcl", line 341, characters 12-65 *)
Theorem for_zenon___C_1_1_1_2_1_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) va)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((
Is_true (_p_V_consistency_rule v1 v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v1))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_partial_match)))))))) va (fun zenon_H10=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule va v2))/\((
Is_true (_p_V_consistency_rule va v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) va))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_partial_match))))))) vb (fun zenon_Hf=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule va vb))/\((Is_true (
_p_V_consistency_rule va v3))/\(~(Is_true (_p_V_consistency_rule vb v3))
)))->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) va))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_1 _p_E_partial_match)))))) vc (fun zenon_He=>(
zenon_imply _ _ (fun zenon_Hd=>(zenon_notand _ _ (fun zenon_Hc=>(
zenon_Hc H1)) (fun zenon_Hb=>(zenon_notand _ _ (fun zenon_Ha=>(zenon_Ha
H11)) (fun zenon_H9=>(zenon_H9 (fun zenon_H8=>(H112 zenon_H8))))
zenon_Hb)) zenon_Hd)) (fun zenon_H7=>(zenon_and _ _ (fun zenon_H5
zenon_H6=>(zenon_G zenon_H5)) zenon_H7)) zenon_He)) zenon_Hf))
zenon_H10)) abst_vote_partial_c1)))).
Qed.

              Theorem __C_1_1_1_2_1_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter va vb vc)) va))).
              assert (__force_use_H112 := H112).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_2_1_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_2_1.
            Section __C_1_1_1_2_2.
(* File "vote.fcl", line 343, character 12, line 344, character 70 *)
Theorem for_zenon___C_1_1_1_2_2_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter vb va vc)) va)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((~
(Is_true (_p_V_consistency_rule v1 v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_partial_match)))))))) vb (fun zenon_H15=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule vb v2))/\((
~(Is_true (_p_V_consistency_rule vb v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vb v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_partial_match))))))) va (fun zenon_H14=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule vb va))/\((~(Is_true (
_p_V_consistency_rule vb v3)))/\(Is_true (_p_V_consistency_rule va v3)))
)->((Is_true (basics._equal_ _ (abst_value (abst_voter vb va v3)) va))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vb va v3)) (
_p_P_constr _p_C_capt_2 _p_E_partial_match)))))) vc (fun zenon_H13=>(
zenon_imply _ _ (fun zenon_H12=>(zenon_notand _ _ (fun zenon_He=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) va (fun zenon_H11=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule va v2))->(Is_true (_p_V_consistency_rule v2 va))))
 vb (fun zenon_H10=>(zenon_imply _ _ (fun zenon_Hf=>(zenon_Hf H1)) (fun
zenon_Hd=>(zenon_He zenon_Hd)) zenon_H10)) zenon_H11))
abst_consistency_rule_is_symmetric)) (fun zenon_Hc=>(zenon_notand _ _ (
fun zenon_Hb=>(zenon_Hb (fun zenon_Ha=>(H112 zenon_Ha)))) (fun
zenon_H9=>(zenon_H9 H11)) zenon_Hc)) zenon_H12)) (fun zenon_H8=>(
zenon_and _ _ (fun zenon_H6 zenon_H7=>(zenon_G zenon_H6)) zenon_H8))
zenon_H13)) zenon_H14)) zenon_H15)) abst_vote_partial_c2)))).
Qed.

              Theorem __C_1_1_1_2_2_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter vb va vc)) va))).
              assert (__force_use_H112 := H112).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_2_2_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_2_2.
            Section __C_1_1_1_2_3.
(* File "vote.fcl", line 346, character 12, line 347, character 70 *)
Theorem for_zenon___C_1_1_1_2_3_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter vc va vb)) va)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((~
(Is_true (_p_V_consistency_rule v1 v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_partial_match)))))))) vc (fun zenon_H19=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule vc v2))/\((
~(Is_true (_p_V_consistency_rule vc v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vc v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_partial_match))))))) va (fun zenon_H18=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule vc va))/\((~(Is_true (
_p_V_consistency_rule vc v3)))/\(Is_true (_p_V_consistency_rule va v3)))
)->((Is_true (basics._equal_ _ (abst_value (abst_voter vc va v3)) va))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vc va v3)) (
_p_P_constr _p_C_capt_2 _p_E_partial_match)))))) vb (fun zenon_H17=>(
zenon_imply _ _ (fun zenon_H16=>(zenon_notand _ _ (fun zenon_H12=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) va (fun zenon_H15=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule va v2))->(Is_true (_p_V_consistency_rule v2 va))))
 vc (fun zenon_H14=>(zenon_imply _ _ (fun zenon_H13=>(zenon_H13 H11)) (
fun zenon_H11=>(zenon_H12 zenon_H11)) zenon_H14)) zenon_H15))
abst_consistency_rule_is_symmetric)) (fun zenon_H10=>(zenon_notand _ _ (
fun zenon_Hf=>(zenon_Hf (fun zenon_Hb=>(zenon_all _p_V_T (fun v1
:_p_V_T=>(forall v2:_p_V_T,((Is_true (_p_V_consistency_rule v1 v2))->(
Is_true (_p_V_consistency_rule v2 v1))))) vc (fun zenon_He=>(zenon_all
_p_V_T (fun v2:_p_V_T=>((Is_true (_p_V_consistency_rule vc v2))->(
Is_true (_p_V_consistency_rule v2 vc)))) vb (fun zenon_Hd=>(zenon_imply
_ _ (fun zenon_Hc=>(zenon_Hc zenon_Hb)) (fun zenon_Ha=>(H112 zenon_Ha))
zenon_Hd)) zenon_He)) abst_consistency_rule_is_symmetric)))) (fun
zenon_H9=>(zenon_H9 H1)) zenon_H10)) zenon_H16)) (fun zenon_H8=>(
zenon_and _ _ (fun zenon_H6 zenon_H7=>(zenon_G zenon_H6)) zenon_H8))
zenon_H17)) zenon_H18)) zenon_H19)) abst_vote_partial_c2)))).
Qed.

              Theorem __C_1_1_1_2_3_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter vc va vb)) va))).
              assert (__force_use_H112 := H112).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_2_3_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_2_3.
            Section __C_1_1_1_2_4.
(* File "vote.fcl", line 351, characters 12-64 *)
Theorem for_zenon___C_1_1_1_2_4_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter va vb vc)) (_p_P_constr _p_C_capt_1
_p_E_partial_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((
Is_true (_p_V_consistency_rule v1 v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v1))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_partial_match)))))))) va (fun zenon_H10=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule va v2))/\((
Is_true (_p_V_consistency_rule va v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) va))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_partial_match))))))) vb (fun zenon_Hf=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule va vb))/\((Is_true (
_p_V_consistency_rule va v3))/\(~(Is_true (_p_V_consistency_rule vb v3))
)))->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) va))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_1 _p_E_partial_match)))))) vc (fun zenon_He=>(
zenon_imply _ _ (fun zenon_Hd=>(zenon_notand _ _ (fun zenon_Hc=>(
zenon_Hc H1)) (fun zenon_Hb=>(zenon_notand _ _ (fun zenon_Ha=>(zenon_Ha
H11)) (fun zenon_H9=>(zenon_H9 (fun zenon_H8=>(H112 zenon_H8))))
zenon_Hb)) zenon_Hd)) (fun zenon_H7=>(zenon_and _ _ (fun zenon_H6
zenon_H5=>(zenon_G zenon_H5)) zenon_H7)) zenon_He)) zenon_Hf))
zenon_H10)) abst_vote_partial_c1)))).
Qed.

              Theorem __C_1_1_1_2_4_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter va vb vc))
                            (_p_P_constr _p_C_capt_1 _p_E_partial_match)))).
              assert (__force_use_H112 := H112).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_2_4_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_2_4.
            Section __C_1_1_1_2_5.
(* File "vote.fcl", line 353, characters 12-82 *)
Theorem for_zenon___C_1_1_1_2_5_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter va vb vc)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter va vb vc)) (_p_P_constr
_p_C_capt_1 _p_E_partial_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_partial_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter va vb vc)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_1 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 n2)) n2))) _p_E_partial_match (fun zenon_H6=>(zenon_subst _
(fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 _p_E_partial_match)) _p_E_partial_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter va vb vc))) _p_E_partial_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_partial_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter va
vb vc))) _p_E_partial_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_1
_p_E_partial_match)) (_p_P_prj_b (abst_diag (abst_voter va vb vc))) (
fun zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter va vb vc)))))) (_p_P_constr
_p_C_capt_1 _p_E_partial_match) (abst_diag (abst_voter va vb vc)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter va vb vc)) (_p_P_constr
_p_C_capt_1 _p_E_partial_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter va vb vc))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter va vb vc))) _p_E_partial_match))) zenon_H7)) zenon_H5
zenon_H6)) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(
zenon_G zenon_H4)) zenon_Hc)) _p_P_partial_match_is_valid))
__C_1_1_1_2_4_LEMMA)))).
Qed.

              Theorem __C_1_1_1_2_5_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter va vb vc))))).
              assert (__force_use_H112 := H112).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_2_5_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_2_5.
            Section __C_1_1_1_2_6.
(* File "vote.fcl", line 357, character 12, line 358, character 67 *)
Theorem for_zenon___C_1_1_1_2_6_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb va vc)) (_p_P_constr _p_C_capt_2
_p_E_partial_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((~
(Is_true (_p_V_consistency_rule v1 v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_partial_match)))))))) vb (fun zenon_H15=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule vb v2))/\((
~(Is_true (_p_V_consistency_rule vb v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vb v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_partial_match))))))) va (fun zenon_H14=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule vb va))/\((~(Is_true (
_p_V_consistency_rule vb v3)))/\(Is_true (_p_V_consistency_rule va v3)))
)->((Is_true (basics._equal_ _ (abst_value (abst_voter vb va v3)) va))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vb va v3)) (
_p_P_constr _p_C_capt_2 _p_E_partial_match)))))) vc (fun zenon_H13=>(
zenon_imply _ _ (fun zenon_H12=>(zenon_notand _ _ (fun zenon_He=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) va (fun zenon_H11=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule va v2))->(Is_true (_p_V_consistency_rule v2 va))))
 vb (fun zenon_H10=>(zenon_imply _ _ (fun zenon_Hf=>(zenon_Hf H1)) (fun
zenon_Hd=>(zenon_He zenon_Hd)) zenon_H10)) zenon_H11))
abst_consistency_rule_is_symmetric)) (fun zenon_Hc=>(zenon_notand _ _ (
fun zenon_Hb=>(zenon_Hb (fun zenon_Ha=>(H112 zenon_Ha)))) (fun
zenon_H9=>(zenon_H9 H11)) zenon_Hc)) zenon_H12)) (fun zenon_H8=>(
zenon_and _ _ (fun zenon_H7 zenon_H6=>(zenon_G zenon_H6)) zenon_H8))
zenon_H13)) zenon_H14)) zenon_H15)) abst_vote_partial_c2)))).
Qed.

              Theorem __C_1_1_1_2_6_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter vb va vc))
                            (_p_P_constr _p_C_capt_2 _p_E_partial_match)))).
              assert (__force_use_H112 := H112).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_2_6_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_2_6.
            Section __C_1_1_1_2_7.
(* File "vote.fcl", line 360, characters 12-82 *)
Theorem for_zenon___C_1_1_1_2_7_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter vb va vc)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter vb va vc)) (_p_P_constr
_p_C_capt_2 _p_E_partial_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_partial_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter vb va vc)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_2 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_2 n2)) n2))) _p_E_partial_match (fun zenon_H6=>(zenon_subst _
(fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_2 _p_E_partial_match)) _p_E_partial_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter vb va vc))) _p_E_partial_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_partial_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vb
va vc))) _p_E_partial_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_2
_p_E_partial_match)) (_p_P_prj_b (abst_diag (abst_voter vb va vc))) (
fun zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter vb va vc)))))) (_p_P_constr
_p_C_capt_2 _p_E_partial_match) (abst_diag (abst_voter vb va vc)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter vb va vc)) (_p_P_constr
_p_C_capt_2 _p_E_partial_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter vb va vc))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter vb va vc))) _p_E_partial_match))) zenon_H7)) zenon_H5
zenon_H6)) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(
zenon_G zenon_H4)) zenon_Hc)) _p_P_partial_match_is_valid))
__C_1_1_1_2_6_LEMMA)))).
Qed.

              Theorem __C_1_1_1_2_7_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter vb va vc))))).
              assert (__force_use_H112 := H112).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_2_7_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_2_7.
            Section __C_1_1_1_2_8.
(* File "vote.fcl", line 364, character 12, line 365, character 67 *)
Theorem for_zenon___C_1_1_1_2_8_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc va vb)) (_p_P_constr _p_C_capt_2
_p_E_partial_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((~
(Is_true (_p_V_consistency_rule v1 v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_partial_match)))))))) vc (fun zenon_H19=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule vc v2))/\((
~(Is_true (_p_V_consistency_rule vc v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vc v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_partial_match))))))) va (fun zenon_H18=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule vc va))/\((~(Is_true (
_p_V_consistency_rule vc v3)))/\(Is_true (_p_V_consistency_rule va v3)))
)->((Is_true (basics._equal_ _ (abst_value (abst_voter vc va v3)) va))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vc va v3)) (
_p_P_constr _p_C_capt_2 _p_E_partial_match)))))) vb (fun zenon_H17=>(
zenon_imply _ _ (fun zenon_H16=>(zenon_notand _ _ (fun zenon_H12=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) va (fun zenon_H15=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule va v2))->(Is_true (_p_V_consistency_rule v2 va))))
 vc (fun zenon_H14=>(zenon_imply _ _ (fun zenon_H13=>(zenon_H13 H11)) (
fun zenon_H11=>(zenon_H12 zenon_H11)) zenon_H14)) zenon_H15))
abst_consistency_rule_is_symmetric)) (fun zenon_H10=>(zenon_notand _ _ (
fun zenon_Hf=>(zenon_Hf (fun zenon_Hb=>(zenon_all _p_V_T (fun v1
:_p_V_T=>(forall v2:_p_V_T,((Is_true (_p_V_consistency_rule v1 v2))->(
Is_true (_p_V_consistency_rule v2 v1))))) vc (fun zenon_He=>(zenon_all
_p_V_T (fun v2:_p_V_T=>((Is_true (_p_V_consistency_rule vc v2))->(
Is_true (_p_V_consistency_rule v2 vc)))) vb (fun zenon_Hd=>(zenon_imply
_ _ (fun zenon_Hc=>(zenon_Hc zenon_Hb)) (fun zenon_Ha=>(H112 zenon_Ha))
zenon_Hd)) zenon_He)) abst_consistency_rule_is_symmetric)))) (fun
zenon_H9=>(zenon_H9 H1)) zenon_H10)) zenon_H16)) (fun zenon_H8=>(
zenon_and _ _ (fun zenon_H7 zenon_H6=>(zenon_G zenon_H6)) zenon_H8))
zenon_H17)) zenon_H18)) zenon_H19)) abst_vote_partial_c2)))).
Qed.

              Theorem __C_1_1_1_2_8_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter vc va vb))
                            (_p_P_constr _p_C_capt_2 _p_E_partial_match)))).
              assert (__force_use_H112 := H112).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_2_8_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_2_8.
            Section __C_1_1_1_2_9.
(* File "vote.fcl", line 367, characters 12-82 *)
Theorem for_zenon___C_1_1_1_2_9_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter vc va vb)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter vc va vb)) (_p_P_constr
_p_C_capt_2 _p_E_partial_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_partial_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter vc va vb)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_2 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_2 n2)) n2))) _p_E_partial_match (fun zenon_H6=>(zenon_subst _
(fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_2 _p_E_partial_match)) _p_E_partial_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter vc va vb))) _p_E_partial_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_partial_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vc
va vb))) _p_E_partial_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_2
_p_E_partial_match)) (_p_P_prj_b (abst_diag (abst_voter vc va vb))) (
fun zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter vc va vb)))))) (_p_P_constr
_p_C_capt_2 _p_E_partial_match) (abst_diag (abst_voter vc va vb)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter vc va vb)) (_p_P_constr
_p_C_capt_2 _p_E_partial_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter vc va vb))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter vc va vb))) _p_E_partial_match))) zenon_H7)) zenon_H5
zenon_H6)) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(
zenon_G zenon_H4)) zenon_Hc)) _p_P_partial_match_is_valid))
__C_1_1_1_2_8_LEMMA)))).
Qed.

              Theorem __C_1_1_1_2_9_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter vc va vb))))).
              assert (__force_use_H112 := H112).
              assert (__force_use_H11 := H11).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_1_2_9_LEMMA;
              auto.
              Qed.
              End __C_1_1_1_2_9.
(* File "vote.fcl", line 369, character 20, line 371, character 39 *)
Theorem for_zenon___C_1_1_1_2_LEMMA:((abst_compatible (abst_voter va vb
vc) (abst_voter vb va vc))/\(abst_compatible (abst_voter va vb vc) (
abst_voter vc va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notand _ _ (fun zenon_H20=>(let zenon_H1f
:=zenon_H20 in (zenon_notor _ _ (fun zenon_H1d zenon_H1e=>(zenon_notand
_ _ (fun zenon_H11=>(zenon_H11 __C_1_1_1_2_5_LEMMA)) (fun zenon_H1c=>(
zenon_notand _ _ (fun zenon_H1b=>(zenon_H1b __C_1_1_1_2_7_LEMMA)) (fun
zenon_H16=>(zenon_all _p_V_T (fun a:_p_V_T=>(Is_true (
_p_V_consistency_rule a a))) (abst_value (abst_voter va vb vc)) (fun
zenon_H9=>(zenon_subst _ (fun zenon_Vi=>(Is_true zenon_Vi)) (
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter va vb vc))) (_p_V_consistency_rule (abst_value (abst_voter
va vb vc)) (abst_value (abst_voter vb va vc))) (fun zenon_H17=>(
zenon_subst _ (fun zenon_Vj=>(~((_p_V_consistency_rule (abst_value (
abst_voter va vb vc)) zenon_Vj) = (_p_V_consistency_rule (abst_value (
abst_voter va vb vc)) (abst_value (abst_voter vb va vc)))))) (
abst_value (abst_voter va vb vc)) (abst_value (abst_voter vb va vc)) (
fun zenon_H18=>(coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (
abst_value (abst_voter va vb vc)) va (fun zenon_Hc=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (abst_value (
abst_voter vb va vc)) va (fun zenon_H19=>(zenon_subst _ (fun zenon_Vk=>(
(abst_value (abst_voter va vb vc)) = zenon_Vk)) va (abst_value (
abst_voter vb va vc)) (fun zenon_H1a=>(zenon_eqsym _ (abst_value (
abst_voter vb va vc)) va zenon_H19 zenon_H1a)) zenon_H18 zenon_Hc))
__C_1_1_1_2_2_LEMMA)) __C_1_1_1_2_1_LEMMA)) (zenon_notnot _ (refl_equal
(_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vb va vc))))) zenon_H17)) zenon_H16 zenon_H9))
_p_V_consistency_rule_reflexive)) zenon_H1c)) zenon_H1d)) zenon_H1f))) (
fun zenon_H15=>(let zenon_H14:=zenon_H15 in (zenon_notor _ _ (fun
zenon_H12 zenon_H13=>(zenon_notand _ _ (fun zenon_H11=>(zenon_H11
__C_1_1_1_2_5_LEMMA)) (fun zenon_H10=>(zenon_notand _ _ (fun zenon_Hf=>(
zenon_Hf __C_1_1_1_2_9_LEMMA)) (fun zenon_H8=>(zenon_all _p_V_T (fun a
:_p_V_T=>(Is_true (_p_V_consistency_rule a a))) (abst_value (abst_voter
va vb vc)) (fun zenon_H9=>(zenon_subst _ (fun zenon_Vf=>(Is_true
zenon_Vf)) (_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (
abst_value (abst_voter va vb vc))) (_p_V_consistency_rule (abst_value (
abst_voter va vb vc)) (abst_value (abst_voter vc va vb))) (fun
zenon_Ha=>(zenon_subst _ (fun zenon_Vg=>(~((_p_V_consistency_rule (
abst_value (abst_voter va vb vc)) zenon_Vg) = (_p_V_consistency_rule (
abst_value (abst_voter va vb vc)) (abst_value (abst_voter vc va vb))))))
 (abst_value (abst_voter va vb vc)) (abst_value (abst_voter vc va vb)) (
fun zenon_Hb=>(coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (
abst_value (abst_voter va vb vc)) va (fun zenon_Hc=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (abst_value (
abst_voter vc va vb)) va (fun zenon_Hd=>(zenon_subst _ (fun zenon_Vh=>((
abst_value (abst_voter va vb vc)) = zenon_Vh)) va (abst_value (
abst_voter vc va vb)) (fun zenon_He=>(zenon_eqsym _ (abst_value (
abst_voter vc va vb)) va zenon_Hd zenon_He)) zenon_Hb zenon_Hc))
__C_1_1_1_2_3_LEMMA)) __C_1_1_1_2_1_LEMMA)) (zenon_notnot _ (refl_equal
(_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vc va vb))))) zenon_Ha)) zenon_H8 zenon_H9))
_p_V_consistency_rule_reflexive)) zenon_H10)) zenon_H12)) zenon_H14)))
zenon_G)))).
Qed.

            Theorem __C_1_1_1_2_LEMMA :
              ((abst_compatible (abst_voter va vb vc) (abst_voter vb va vc)) /\
                 (abst_compatible (abst_voter va vb vc)
                   (abst_voter vc va vb))).
            assert (__force_use_H112 := H112).
            assert (__force_use_H11 := H11).
            assert (__force_use_H1 := H1).
            apply for_zenon___C_1_1_1_2_LEMMA;
            auto.
            Qed.
            End __C_1_1_1_2.
(* File "vote.fcl", line 373, characters 17-55 *)
Theorem for_zenon___C_1_1_1_LEMMA:((abst_compatible (abst_voter va vb
vc) (abst_voter vb va vc))/\(abst_compatible (abst_voter va vb vc) (
abst_voter vc va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_imply _ _ (fun zenon_H5=>(zenon_imply _ _ (
fun zenon_H6=>(zenon_H6 zenon_H5)) (fun zenon_H4=>(zenon_G zenon_H4))
__C_1_1_1_2_LEMMA)) (fun zenon_H4=>(zenon_G zenon_H4))
__C_1_1_1_1_LEMMA)))).
Qed.

          Theorem __C_1_1_1_LEMMA :
            ((abst_compatible (abst_voter va vb vc) (abst_voter vb va vc)) /\
               (abst_compatible (abst_voter va vb vc) (abst_voter vc va vb))).
          assert (__force_use_H11 := H11).
          assert (__force_use_H1 := H1).
          apply for_zenon___C_1_1_1_LEMMA;
          auto.
          Qed.
          End __C_1_1_1.
        Section __C_1_1_2.
          Variable H12 : ~Is_true (((_p_V_consistency_rule va vc))).
          Section __C_1_1_2_1.
            Variable H121 : Is_true ((_p_V_consistency_rule vb vc)).
            Section __C_1_1_2_1_1.
(* File "vote.fcl", line 389, characters 10-63 *)
Theorem for_zenon___C_1_1_2_1_1_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vb)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((~
(Is_true (_p_V_consistency_rule v1 v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_partial_match)))))))) va (fun zenon_H10=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule va v2))/\((
~(Is_true (_p_V_consistency_rule va v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_partial_match))))))) vb (fun zenon_Hf=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule va vb))/\((~(Is_true (
_p_V_consistency_rule va v3)))/\(Is_true (_p_V_consistency_rule vb v3)))
)->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) vb))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_2 _p_E_partial_match)))))) vc (fun zenon_He=>(
zenon_imply _ _ (fun zenon_Hd=>(zenon_notand _ _ (fun zenon_Hc=>(
zenon_Hc H1)) (fun zenon_Hb=>(zenon_notand _ _ (fun zenon_Ha=>(zenon_Ha
(fun zenon_H9=>(H12 zenon_H9)))) (fun zenon_H8=>(zenon_H8 H121))
zenon_Hb)) zenon_Hd)) (fun zenon_H7=>(zenon_and _ _ (fun zenon_H5
zenon_H6=>(zenon_G zenon_H5)) zenon_H7)) zenon_He)) zenon_Hf))
zenon_H10)) abst_vote_partial_c2)))).
Qed.

              Theorem __C_1_1_2_1_1_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter va vb vc)) vb))).
              assert (__force_use_H121 := H121).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_1_1_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_1_1.
            Section __C_1_1_2_1_2.
(* File "vote.fcl", line 391, character 10, line 392, character 68 *)
Theorem for_zenon___C_1_1_2_1_2_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter vb va vc)) vb)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((
Is_true (_p_V_consistency_rule v1 v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v1))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_partial_match)))))))) vb (fun zenon_H15=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule vb v2))/\((
Is_true (_p_V_consistency_rule vb v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vb v2 v3)) vb))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_partial_match))))))) va (fun zenon_H14=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule vb va))/\((Is_true (
_p_V_consistency_rule vb v3))/\(~(Is_true (_p_V_consistency_rule va v3))
)))->((Is_true (basics._equal_ _ (abst_value (abst_voter vb va v3)) vb))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vb va v3)) (
_p_P_constr _p_C_capt_1 _p_E_partial_match)))))) vc (fun zenon_H13=>(
zenon_imply _ _ (fun zenon_H12=>(zenon_notand _ _ (fun zenon_He=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) va (fun zenon_H11=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule va v2))->(Is_true (_p_V_consistency_rule v2 va))))
 vb (fun zenon_H10=>(zenon_imply _ _ (fun zenon_Hf=>(zenon_Hf H1)) (fun
zenon_Hd=>(zenon_He zenon_Hd)) zenon_H10)) zenon_H11))
abst_consistency_rule_is_symmetric)) (fun zenon_Hc=>(zenon_notand _ _ (
fun zenon_Hb=>(zenon_Hb H121)) (fun zenon_Ha=>(zenon_Ha (fun zenon_H9=>(
H12 zenon_H9)))) zenon_Hc)) zenon_H12)) (fun zenon_H8=>(zenon_and _ _ (
fun zenon_H6 zenon_H7=>(zenon_G zenon_H6)) zenon_H8)) zenon_H13))
zenon_H14)) zenon_H15)) abst_vote_partial_c1)))).
Qed.

              Theorem __C_1_1_2_1_2_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter vb va vc)) vb))).
              assert (__force_use_H121 := H121).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_1_2_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_1_2.
            Section __C_1_1_2_1_3.
(* File "vote.fcl", line 394, character 10, line 395, character 68 *)
Theorem for_zenon___C_1_1_2_1_3_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter vc va vb)) vb)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((Is_true (_p_V_consistency_rule v1 v3))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_partial_match)))))))) vc (fun zenon_H19=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule vc v2)))
/\((Is_true (_p_V_consistency_rule vc v3))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vc v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_partial_match))))))) va (fun zenon_H18=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule vc va)))/\((Is_true (
_p_V_consistency_rule vc v3))/\(Is_true (_p_V_consistency_rule va v3))))
->((Is_true (basics._equal_ _ (abst_value (abst_voter vc va v3)) v3))/\(
Is_true (basics._equal_ _ (abst_diag (abst_voter vc va v3)) (
_p_P_constr _p_C_capt_3 _p_E_partial_match)))))) vb (fun zenon_H17=>(
zenon_imply _ _ (fun zenon_H16=>(zenon_notand _ _ (fun zenon_H15=>(
zenon_H15 (fun zenon_H11=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,((Is_true (_p_V_consistency_rule v1 v2))->(Is_true (
_p_V_consistency_rule v2 v1))))) vc (fun zenon_H14=>(zenon_all _p_V_T (
fun v2:_p_V_T=>((Is_true (_p_V_consistency_rule vc v2))->(Is_true (
_p_V_consistency_rule v2 vc)))) va (fun zenon_H13=>(zenon_imply _ _ (
fun zenon_H12=>(zenon_H12 zenon_H11)) (fun zenon_H10=>(H12 zenon_H10))
zenon_H13)) zenon_H14)) abst_consistency_rule_is_symmetric)))) (fun
zenon_Hf=>(zenon_notand _ _ (fun zenon_Hb=>(zenon_all _p_V_T (fun v1
:_p_V_T=>(forall v2:_p_V_T,((Is_true (_p_V_consistency_rule v1 v2))->(
Is_true (_p_V_consistency_rule v2 v1))))) vb (fun zenon_He=>(zenon_all
_p_V_T (fun v2:_p_V_T=>((Is_true (_p_V_consistency_rule vb v2))->(
Is_true (_p_V_consistency_rule v2 vb)))) vc (fun zenon_Hd=>(zenon_imply
_ _ (fun zenon_Hc=>(zenon_Hc H121)) (fun zenon_Ha=>(zenon_Hb zenon_Ha))
zenon_Hd)) zenon_He)) abst_consistency_rule_is_symmetric)) (fun
zenon_H9=>(zenon_H9 H1)) zenon_Hf)) zenon_H16)) (fun zenon_H8=>(
zenon_and _ _ (fun zenon_H6 zenon_H7=>(zenon_G zenon_H6)) zenon_H8))
zenon_H17)) zenon_H18)) zenon_H19)) abst_vote_partial_c3)))).
Qed.

              Theorem __C_1_1_2_1_3_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter vc va vb)) vb))).
              assert (__force_use_H121 := H121).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_1_3_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_1_3.
            Section __C_1_1_2_1_4.
(* File "vote.fcl", line 399, characters 10-62 *)
Theorem for_zenon___C_1_1_2_1_4_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter va vb vc)) (_p_P_constr _p_C_capt_2
_p_E_partial_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((~
(Is_true (_p_V_consistency_rule v1 v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_partial_match)))))))) va (fun zenon_H10=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule va v2))/\((
~(Is_true (_p_V_consistency_rule va v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_partial_match))))))) vb (fun zenon_Hf=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule va vb))/\((~(Is_true (
_p_V_consistency_rule va v3)))/\(Is_true (_p_V_consistency_rule vb v3)))
)->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) vb))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_2 _p_E_partial_match)))))) vc (fun zenon_He=>(
zenon_imply _ _ (fun zenon_Hd=>(zenon_notand _ _ (fun zenon_Hc=>(
zenon_Hc H1)) (fun zenon_Hb=>(zenon_notand _ _ (fun zenon_Ha=>(zenon_Ha
(fun zenon_H9=>(H12 zenon_H9)))) (fun zenon_H8=>(zenon_H8 H121))
zenon_Hb)) zenon_Hd)) (fun zenon_H7=>(zenon_and _ _ (fun zenon_H6
zenon_H5=>(zenon_G zenon_H5)) zenon_H7)) zenon_He)) zenon_Hf))
zenon_H10)) abst_vote_partial_c2)))).
Qed.

              Theorem __C_1_1_2_1_4_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter va vb vc))
                            (_p_P_constr _p_C_capt_2 _p_E_partial_match)))).
              assert (__force_use_H121 := H121).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_1_4_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_1_4.
            Section __C_1_1_2_1_5.
(* File "vote.fcl", line 401, characters 12-82 *)
Theorem for_zenon___C_1_1_2_1_5_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter va vb vc)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter va vb vc)) (_p_P_constr
_p_C_capt_2 _p_E_partial_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_partial_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter va vb vc)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_2 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_2 n2)) n2))) _p_E_partial_match (fun zenon_H6=>(zenon_subst _
(fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_2 _p_E_partial_match)) _p_E_partial_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter va vb vc))) _p_E_partial_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_partial_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter va
vb vc))) _p_E_partial_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_2
_p_E_partial_match)) (_p_P_prj_b (abst_diag (abst_voter va vb vc))) (
fun zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter va vb vc)))))) (_p_P_constr
_p_C_capt_2 _p_E_partial_match) (abst_diag (abst_voter va vb vc)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter va vb vc)) (_p_P_constr
_p_C_capt_2 _p_E_partial_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter va vb vc))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter va vb vc))) _p_E_partial_match))) zenon_H7)) zenon_H5
zenon_H6)) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(
zenon_G zenon_H4)) zenon_Hc)) _p_P_partial_match_is_valid))
__C_1_1_2_1_4_LEMMA)))).
Qed.

              Theorem __C_1_1_2_1_5_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter va vb vc))))).
              assert (__force_use_H121 := H121).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_1_5_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_1_5.
            Section __C_1_1_2_1_6.
(* File "vote.fcl", line 405, character 11, line 406, character 66 *)
Theorem for_zenon___C_1_1_2_1_6_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb va vc)) (_p_P_constr _p_C_capt_1
_p_E_partial_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((
Is_true (_p_V_consistency_rule v1 v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v1))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_partial_match)))))))) vb (fun zenon_H15=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule vb v2))/\((
Is_true (_p_V_consistency_rule vb v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vb v2 v3)) vb))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_partial_match))))))) va (fun zenon_H14=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule vb va))/\((Is_true (
_p_V_consistency_rule vb v3))/\(~(Is_true (_p_V_consistency_rule va v3))
)))->((Is_true (basics._equal_ _ (abst_value (abst_voter vb va v3)) vb))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vb va v3)) (
_p_P_constr _p_C_capt_1 _p_E_partial_match)))))) vc (fun zenon_H13=>(
zenon_imply _ _ (fun zenon_H12=>(zenon_notand _ _ (fun zenon_He=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) va (fun zenon_H11=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule va v2))->(Is_true (_p_V_consistency_rule v2 va))))
 vb (fun zenon_H10=>(zenon_imply _ _ (fun zenon_Hf=>(zenon_Hf H1)) (fun
zenon_Hd=>(zenon_He zenon_Hd)) zenon_H10)) zenon_H11))
abst_consistency_rule_is_symmetric)) (fun zenon_Hc=>(zenon_notand _ _ (
fun zenon_Hb=>(zenon_Hb H121)) (fun zenon_Ha=>(zenon_Ha (fun zenon_H9=>(
H12 zenon_H9)))) zenon_Hc)) zenon_H12)) (fun zenon_H8=>(zenon_and _ _ (
fun zenon_H7 zenon_H6=>(zenon_G zenon_H6)) zenon_H8)) zenon_H13))
zenon_H14)) zenon_H15)) abst_vote_partial_c1)))).
Qed.

              Theorem __C_1_1_2_1_6_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter vb va vc))
                            (_p_P_constr _p_C_capt_1 _p_E_partial_match)))).
              assert (__force_use_H121 := H121).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_1_6_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_1_6.
            Section __C_1_1_2_1_7.
(* File "vote.fcl", line 408, characters 11-81 *)
Theorem for_zenon___C_1_1_2_1_7_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter vb va vc)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter vb va vc)) (_p_P_constr
_p_C_capt_1 _p_E_partial_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_partial_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter vb va vc)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_1 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 n2)) n2))) _p_E_partial_match (fun zenon_H6=>(zenon_subst _
(fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 _p_E_partial_match)) _p_E_partial_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter vb va vc))) _p_E_partial_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_partial_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vb
va vc))) _p_E_partial_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_1
_p_E_partial_match)) (_p_P_prj_b (abst_diag (abst_voter vb va vc))) (
fun zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter vb va vc)))))) (_p_P_constr
_p_C_capt_1 _p_E_partial_match) (abst_diag (abst_voter vb va vc)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter vb va vc)) (_p_P_constr
_p_C_capt_1 _p_E_partial_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter vb va vc))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter vb va vc))) _p_E_partial_match))) zenon_H7)) zenon_H5
zenon_H6)) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(
zenon_G zenon_H4)) zenon_Hc)) _p_P_partial_match_is_valid))
__C_1_1_2_1_6_LEMMA)))).
Qed.

              Theorem __C_1_1_2_1_7_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter vb va vc))))).
              assert (__force_use_H121 := H121).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_1_7_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_1_7.
            Section __C_1_1_2_1_8.
(* File "vote.fcl", line 412, character 11, line 413, character 66 *)
Theorem for_zenon___C_1_1_2_1_8_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc va vb)) (_p_P_constr _p_C_capt_3
_p_E_partial_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((Is_true (_p_V_consistency_rule v1 v3))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_partial_match)))))))) vc (fun zenon_H19=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule vc v2)))
/\((Is_true (_p_V_consistency_rule vc v3))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vc v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_partial_match))))))) va (fun zenon_H18=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule vc va)))/\((Is_true (
_p_V_consistency_rule vc v3))/\(Is_true (_p_V_consistency_rule va v3))))
->((Is_true (basics._equal_ _ (abst_value (abst_voter vc va v3)) v3))/\(
Is_true (basics._equal_ _ (abst_diag (abst_voter vc va v3)) (
_p_P_constr _p_C_capt_3 _p_E_partial_match)))))) vb (fun zenon_H17=>(
zenon_imply _ _ (fun zenon_H16=>(zenon_notand _ _ (fun zenon_H15=>(
zenon_H15 (fun zenon_H11=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,((Is_true (_p_V_consistency_rule v1 v2))->(Is_true (
_p_V_consistency_rule v2 v1))))) vc (fun zenon_H14=>(zenon_all _p_V_T (
fun v2:_p_V_T=>((Is_true (_p_V_consistency_rule vc v2))->(Is_true (
_p_V_consistency_rule v2 vc)))) va (fun zenon_H13=>(zenon_imply _ _ (
fun zenon_H12=>(zenon_H12 zenon_H11)) (fun zenon_H10=>(H12 zenon_H10))
zenon_H13)) zenon_H14)) abst_consistency_rule_is_symmetric)))) (fun
zenon_Hf=>(zenon_notand _ _ (fun zenon_Hb=>(zenon_all _p_V_T (fun v1
:_p_V_T=>(forall v2:_p_V_T,((Is_true (_p_V_consistency_rule v1 v2))->(
Is_true (_p_V_consistency_rule v2 v1))))) vb (fun zenon_He=>(zenon_all
_p_V_T (fun v2:_p_V_T=>((Is_true (_p_V_consistency_rule vb v2))->(
Is_true (_p_V_consistency_rule v2 vb)))) vc (fun zenon_Hd=>(zenon_imply
_ _ (fun zenon_Hc=>(zenon_Hc H121)) (fun zenon_Ha=>(zenon_Hb zenon_Ha))
zenon_Hd)) zenon_He)) abst_consistency_rule_is_symmetric)) (fun
zenon_H9=>(zenon_H9 H1)) zenon_Hf)) zenon_H16)) (fun zenon_H8=>(
zenon_and _ _ (fun zenon_H7 zenon_H6=>(zenon_G zenon_H6)) zenon_H8))
zenon_H17)) zenon_H18)) zenon_H19)) abst_vote_partial_c3)))).
Qed.

              Theorem __C_1_1_2_1_8_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter vc va vb))
                            (_p_P_constr _p_C_capt_3 _p_E_partial_match)))).
              assert (__force_use_H121 := H121).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_1_8_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_1_8.
            Section __C_1_1_2_1_9.
(* File "vote.fcl", line 415, characters 11-81 *)
Theorem for_zenon___C_1_1_2_1_9_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter vc va vb)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter vc va vb)) (_p_P_constr
_p_C_capt_3 _p_E_partial_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_partial_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter vc va vb)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_3 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_3 n2)) n2))) _p_E_partial_match (fun zenon_H6=>(zenon_subst _
(fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_3 _p_E_partial_match)) _p_E_partial_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter vc va vb))) _p_E_partial_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_partial_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vc
va vb))) _p_E_partial_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_3
_p_E_partial_match)) (_p_P_prj_b (abst_diag (abst_voter vc va vb))) (
fun zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter vc va vb)))))) (_p_P_constr
_p_C_capt_3 _p_E_partial_match) (abst_diag (abst_voter vc va vb)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter vc va vb)) (_p_P_constr
_p_C_capt_3 _p_E_partial_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter vc va vb))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter vc va vb))) _p_E_partial_match))) zenon_H7)) zenon_H5
zenon_H6)) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(
zenon_G zenon_H4)) zenon_Hc)) _p_P_partial_match_is_valid))
__C_1_1_2_1_8_LEMMA)))).
Qed.

              Theorem __C_1_1_2_1_9_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter vc va vb))))).
              assert (__force_use_H121 := H121).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_1_9_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_1_9.
(* File "vote.fcl", line 416, character 19, line 418, character 37 *)
Theorem for_zenon___C_1_1_2_1_LEMMA:((abst_compatible (abst_voter va vb
vc) (abst_voter vb va vc))/\(abst_compatible (abst_voter va vb vc) (
abst_voter vc va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notand _ _ (fun zenon_H20=>(let zenon_H1f
:=zenon_H20 in (zenon_notor _ _ (fun zenon_H1d zenon_H1e=>(zenon_notand
_ _ (fun zenon_H11=>(zenon_H11 __C_1_1_2_1_5_LEMMA)) (fun zenon_H1c=>(
zenon_notand _ _ (fun zenon_H1b=>(zenon_H1b __C_1_1_2_1_7_LEMMA)) (fun
zenon_H16=>(zenon_all _p_V_T (fun a:_p_V_T=>(Is_true (
_p_V_consistency_rule a a))) (abst_value (abst_voter va vb vc)) (fun
zenon_H9=>(zenon_subst _ (fun zenon_Vi=>(Is_true zenon_Vi)) (
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter va vb vc))) (_p_V_consistency_rule (abst_value (abst_voter
va vb vc)) (abst_value (abst_voter vb va vc))) (fun zenon_H17=>(
zenon_subst _ (fun zenon_Vj=>(~((_p_V_consistency_rule (abst_value (
abst_voter va vb vc)) zenon_Vj) = (_p_V_consistency_rule (abst_value (
abst_voter va vb vc)) (abst_value (abst_voter vb va vc)))))) (
abst_value (abst_voter va vb vc)) (abst_value (abst_voter vb va vc)) (
fun zenon_H18=>(coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (
abst_value (abst_voter va vb vc)) vb (fun zenon_Hc=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (abst_value (
abst_voter vb va vc)) vb (fun zenon_H19=>(zenon_subst _ (fun zenon_Vk=>(
(abst_value (abst_voter va vb vc)) = zenon_Vk)) vb (abst_value (
abst_voter vb va vc)) (fun zenon_H1a=>(zenon_eqsym _ (abst_value (
abst_voter vb va vc)) vb zenon_H19 zenon_H1a)) zenon_H18 zenon_Hc))
__C_1_1_2_1_2_LEMMA)) __C_1_1_2_1_1_LEMMA)) (zenon_notnot _ (refl_equal
(_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vb va vc))))) zenon_H17)) zenon_H16 zenon_H9))
_p_V_consistency_rule_reflexive)) zenon_H1c)) zenon_H1d)) zenon_H1f))) (
fun zenon_H15=>(let zenon_H14:=zenon_H15 in (zenon_notor _ _ (fun
zenon_H12 zenon_H13=>(zenon_notand _ _ (fun zenon_H11=>(zenon_H11
__C_1_1_2_1_5_LEMMA)) (fun zenon_H10=>(zenon_notand _ _ (fun zenon_Hf=>(
zenon_Hf __C_1_1_2_1_9_LEMMA)) (fun zenon_H8=>(zenon_all _p_V_T (fun a
:_p_V_T=>(Is_true (_p_V_consistency_rule a a))) (abst_value (abst_voter
va vb vc)) (fun zenon_H9=>(zenon_subst _ (fun zenon_Vf=>(Is_true
zenon_Vf)) (_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (
abst_value (abst_voter va vb vc))) (_p_V_consistency_rule (abst_value (
abst_voter va vb vc)) (abst_value (abst_voter vc va vb))) (fun
zenon_Ha=>(zenon_subst _ (fun zenon_Vg=>(~((_p_V_consistency_rule (
abst_value (abst_voter va vb vc)) zenon_Vg) = (_p_V_consistency_rule (
abst_value (abst_voter va vb vc)) (abst_value (abst_voter vc va vb))))))
 (abst_value (abst_voter va vb vc)) (abst_value (abst_voter vc va vb)) (
fun zenon_Hb=>(coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (
abst_value (abst_voter va vb vc)) vb (fun zenon_Hc=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (abst_value (
abst_voter vc va vb)) vb (fun zenon_Hd=>(zenon_subst _ (fun zenon_Vh=>((
abst_value (abst_voter va vb vc)) = zenon_Vh)) vb (abst_value (
abst_voter vc va vb)) (fun zenon_He=>(zenon_eqsym _ (abst_value (
abst_voter vc va vb)) vb zenon_Hd zenon_He)) zenon_Hb zenon_Hc))
__C_1_1_2_1_3_LEMMA)) __C_1_1_2_1_1_LEMMA)) (zenon_notnot _ (refl_equal
(_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vc va vb))))) zenon_Ha)) zenon_H8 zenon_H9))
_p_V_consistency_rule_reflexive)) zenon_H10)) zenon_H12)) zenon_H14)))
zenon_G)))).
Qed.

            Theorem __C_1_1_2_1_LEMMA :
              ((abst_compatible (abst_voter va vb vc) (abst_voter vb va vc)) /\
                 (abst_compatible (abst_voter va vb vc)
                   (abst_voter vc va vb))).
            assert (__force_use_H121 := H121).
            assert (__force_use_H12 := H12).
            assert (__force_use_H1 := H1).
            apply for_zenon___C_1_1_2_1_LEMMA;
            auto.
            Qed.
            End __C_1_1_2_1.
          Section __C_1_1_2_2.
            Variable H122 : ~Is_true (((_p_V_consistency_rule vb vc))).
            Section __C_1_1_2_2_1.
(* File "vote.fcl", line 427, character 10, line 428, character 66 *)
Theorem for_zenon___C_1_1_2_2_1_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) va)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((~
(Is_true (_p_V_consistency_rule v1 v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v1))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_range_match)))))))) va (fun zenon_H12=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule va v2))/\((
~(Is_true (_p_V_consistency_rule va v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) va))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_range_match))))))) vb (fun zenon_H11=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule va vb))/\((~(Is_true (
_p_V_consistency_rule va v3)))/\(~(Is_true (_p_V_consistency_rule vb v3)
))))->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) va)
)/\(Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_3 _p_E_range_match)))))) vc (fun zenon_H10=>(
zenon_imply _ _ (fun zenon_Hf=>(zenon_notand _ _ (fun zenon_He=>(
zenon_He H1)) (fun zenon_Hd=>(zenon_notand _ _ (fun zenon_Hc=>(zenon_Hc
(fun zenon_Hb=>(H12 zenon_Hb)))) (fun zenon_Ha=>(zenon_Ha (fun
zenon_H9=>(H122 zenon_H9)))) zenon_Hd)) zenon_Hf)) (fun zenon_H8=>(
zenon_and _ _ (fun zenon_H6 zenon_H7=>(zenon_G zenon_H6)) zenon_H8))
zenon_H10)) zenon_H11)) zenon_H12)) abst_vote_match_c3)))).
Qed.

              Theorem __C_1_1_2_2_1_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter va vb vc)) va))).
              assert (__force_use_H122 := H122).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_2_1_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_2_1.
            Section __C_1_1_2_2_2.
(* File "vote.fcl", line 430, character 10, line 431, character 66 *)
Theorem for_zenon___C_1_1_2_2_2_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter vb va vc)) vb)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((~
(Is_true (_p_V_consistency_rule v1 v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v1))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_range_match)))))))) vb (fun zenon_H16=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule vb v2))/\((
~(Is_true (_p_V_consistency_rule vb v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vb v2 v3)) vb))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_range_match))))))) va (fun zenon_H15=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule vb va))/\((~(Is_true (
_p_V_consistency_rule vb v3)))/\(~(Is_true (_p_V_consistency_rule va v3)
))))->((Is_true (basics._equal_ _ (abst_value (abst_voter vb va v3)) vb)
)/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vb va v3)) (
_p_P_constr _p_C_capt_3 _p_E_range_match)))))) vc (fun zenon_H14=>(
zenon_imply _ _ (fun zenon_H13=>(zenon_notand _ _ (fun zenon_Hf=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) va (fun zenon_H12=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule va v2))->(Is_true (_p_V_consistency_rule v2 va))))
 vb (fun zenon_H11=>(zenon_imply _ _ (fun zenon_H10=>(zenon_H10 H1)) (
fun zenon_He=>(zenon_Hf zenon_He)) zenon_H11)) zenon_H12))
abst_consistency_rule_is_symmetric)) (fun zenon_Hd=>(zenon_notand _ _ (
fun zenon_Hc=>(zenon_Hc (fun zenon_Hb=>(H122 zenon_Hb)))) (fun
zenon_Ha=>(zenon_Ha (fun zenon_H9=>(H12 zenon_H9)))) zenon_Hd))
zenon_H13)) (fun zenon_H8=>(zenon_and _ _ (fun zenon_H6 zenon_H7=>(
zenon_G zenon_H6)) zenon_H8)) zenon_H14)) zenon_H15)) zenon_H16))
abst_vote_match_c3)))).
Qed.

              Theorem __C_1_1_2_2_2_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter vb va vc)) vb))).
              assert (__force_use_H122 := H122).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_2_2_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_2_2.
            Section __C_1_1_2_2_3.
(* File "vote.fcl", line 433, character 10, line 434, character 66 *)
Theorem for_zenon___C_1_1_2_2_3_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter vc va vb)) va)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((~(Is_true (_p_V_consistency_rule v1 v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_range_match)))))))) vc (fun zenon_H19=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule vc v2)))
/\((~(Is_true (_p_V_consistency_rule vc v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vc v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_range_match))))))) va (fun zenon_H18=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule vc va)))/\((~(Is_true (
_p_V_consistency_rule vc v3)))/\(Is_true (_p_V_consistency_rule va v3)))
)->((Is_true (basics._equal_ _ (abst_value (abst_voter vc va v3)) va))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vc va v3)) (
_p_P_constr _p_C_capt_1 _p_E_range_match)))))) vb (fun zenon_H17=>(
zenon_imply _ _ (fun zenon_H16=>(zenon_notand _ _ (fun zenon_H15=>(
zenon_H15 (fun zenon_H12=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,((Is_true (_p_V_consistency_rule v1 v2))->(Is_true (
_p_V_consistency_rule v2 v1))))) vc (fun zenon_He=>(zenon_all _p_V_T (
fun v2:_p_V_T=>((Is_true (_p_V_consistency_rule vc v2))->(Is_true (
_p_V_consistency_rule v2 vc)))) va (fun zenon_H14=>(zenon_imply _ _ (
fun zenon_H13=>(zenon_H13 zenon_H12)) (fun zenon_H11=>(H12 zenon_H11))
zenon_H14)) zenon_He)) abst_consistency_rule_is_symmetric)))) (fun
zenon_H10=>(zenon_notand _ _ (fun zenon_Hf=>(zenon_Hf (fun zenon_Hb=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) vc (fun zenon_He=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule vc v2))->(Is_true (_p_V_consistency_rule v2 vc))))
 vb (fun zenon_Hd=>(zenon_imply _ _ (fun zenon_Hc=>(zenon_Hc zenon_Hb))
(fun zenon_Ha=>(H122 zenon_Ha)) zenon_Hd)) zenon_He))
abst_consistency_rule_is_symmetric)))) (fun zenon_H9=>(zenon_H9 H1))
zenon_H10)) zenon_H16)) (fun zenon_H8=>(zenon_and _ _ (fun zenon_H6
zenon_H7=>(zenon_G zenon_H6)) zenon_H8)) zenon_H17)) zenon_H18))
zenon_H19)) abst_vote_match_c1)))).
Qed.

              Theorem __C_1_1_2_2_3_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter vc va vb)) va))).
              assert (__force_use_H122 := H122).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_2_3_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_2_3.
            Section __C_1_1_2_2_4.
(* File "vote.fcl", line 438, character 10, line 439, character 63 *)
Theorem for_zenon___C_1_1_2_2_4_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter va vb vc)) (_p_P_constr _p_C_capt_3
_p_E_range_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((~
(Is_true (_p_V_consistency_rule v1 v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v1))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_range_match)))))))) va (fun zenon_H12=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule va v2))/\((
~(Is_true (_p_V_consistency_rule va v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) va))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_range_match))))))) vb (fun zenon_H11=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule va vb))/\((~(Is_true (
_p_V_consistency_rule va v3)))/\(~(Is_true (_p_V_consistency_rule vb v3)
))))->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) va)
)/\(Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_3 _p_E_range_match)))))) vc (fun zenon_H10=>(
zenon_imply _ _ (fun zenon_Hf=>(zenon_notand _ _ (fun zenon_He=>(
zenon_He H1)) (fun zenon_Hd=>(zenon_notand _ _ (fun zenon_Hc=>(zenon_Hc
(fun zenon_Hb=>(H12 zenon_Hb)))) (fun zenon_Ha=>(zenon_Ha (fun
zenon_H9=>(H122 zenon_H9)))) zenon_Hd)) zenon_Hf)) (fun zenon_H8=>(
zenon_and _ _ (fun zenon_H7 zenon_H6=>(zenon_G zenon_H6)) zenon_H8))
zenon_H10)) zenon_H11)) zenon_H12)) abst_vote_match_c3)))).
Qed.

              Theorem __C_1_1_2_2_4_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter va vb vc))
                            (_p_P_constr _p_C_capt_3 _p_E_range_match)))).
              assert (__force_use_H122 := H122).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_2_4_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_2_4.
            Section __C_1_1_2_2_5.
(* File "vote.fcl", line 441, characters 12-80 *)
Theorem for_zenon___C_1_1_2_2_5_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter va vb vc)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter va vb vc)) (_p_P_constr
_p_C_capt_3 _p_E_range_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_range_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter va vb vc)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_3 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_3 n2)) n2))) _p_E_range_match (fun zenon_H6=>(zenon_subst _ (
fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_3 _p_E_range_match)) _p_E_range_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter va vb vc))) _p_E_range_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_range_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter va
vb vc))) _p_E_range_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_3
_p_E_range_match)) (_p_P_prj_b (abst_diag (abst_voter va vb vc))) (fun
zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter va vb vc)))))) (_p_P_constr
_p_C_capt_3 _p_E_range_match) (abst_diag (abst_voter va vb vc)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter va vb vc)) (_p_P_constr
_p_C_capt_3 _p_E_range_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter va vb vc))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter va vb vc))) _p_E_range_match))) zenon_H7)) zenon_H5 zenon_H6)
) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(zenon_G
zenon_H4)) zenon_Hc)) _p_P_range_match_is_valid)) __C_1_1_2_2_4_LEMMA)))
).
Qed.

              Theorem __C_1_1_2_2_5_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter va vb vc))))).
              assert (__force_use_H122 := H122).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_2_5_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_2_5.
            Section __C_1_1_2_2_6.
(* File "vote.fcl", line 445, character 11, line 446, character 64 *)
Theorem for_zenon___C_1_1_2_2_6_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb va vc)) (_p_P_constr _p_C_capt_3
_p_E_range_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((~
(Is_true (_p_V_consistency_rule v1 v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v1))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_range_match)))))))) vb (fun zenon_H16=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule vb v2))/\((
~(Is_true (_p_V_consistency_rule vb v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vb v2 v3)) vb))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_range_match))))))) va (fun zenon_H15=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule vb va))/\((~(Is_true (
_p_V_consistency_rule vb v3)))/\(~(Is_true (_p_V_consistency_rule va v3)
))))->((Is_true (basics._equal_ _ (abst_value (abst_voter vb va v3)) vb)
)/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vb va v3)) (
_p_P_constr _p_C_capt_3 _p_E_range_match)))))) vc (fun zenon_H14=>(
zenon_imply _ _ (fun zenon_H13=>(zenon_notand _ _ (fun zenon_Hf=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) va (fun zenon_H12=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule va v2))->(Is_true (_p_V_consistency_rule v2 va))))
 vb (fun zenon_H11=>(zenon_imply _ _ (fun zenon_H10=>(zenon_H10 H1)) (
fun zenon_He=>(zenon_Hf zenon_He)) zenon_H11)) zenon_H12))
abst_consistency_rule_is_symmetric)) (fun zenon_Hd=>(zenon_notand _ _ (
fun zenon_Hc=>(zenon_Hc (fun zenon_Hb=>(H122 zenon_Hb)))) (fun
zenon_Ha=>(zenon_Ha (fun zenon_H9=>(H12 zenon_H9)))) zenon_Hd))
zenon_H13)) (fun zenon_H8=>(zenon_and _ _ (fun zenon_H7 zenon_H6=>(
zenon_G zenon_H6)) zenon_H8)) zenon_H14)) zenon_H15)) zenon_H16))
abst_vote_match_c3)))).
Qed.

              Theorem __C_1_1_2_2_6_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter vb va vc))
                            (_p_P_constr _p_C_capt_3 _p_E_range_match)))).
              assert (__force_use_H122 := H122).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_2_6_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_2_6.
            Section __C_1_1_2_2_7.
(* File "vote.fcl", line 448, characters 11-79 *)
Theorem for_zenon___C_1_1_2_2_7_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter vb va vc)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter vb va vc)) (_p_P_constr
_p_C_capt_3 _p_E_range_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_range_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter vb va vc)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_3 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_3 n2)) n2))) _p_E_range_match (fun zenon_H6=>(zenon_subst _ (
fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_3 _p_E_range_match)) _p_E_range_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter vb va vc))) _p_E_range_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_range_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vb
va vc))) _p_E_range_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_3
_p_E_range_match)) (_p_P_prj_b (abst_diag (abst_voter vb va vc))) (fun
zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter vb va vc)))))) (_p_P_constr
_p_C_capt_3 _p_E_range_match) (abst_diag (abst_voter vb va vc)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter vb va vc)) (_p_P_constr
_p_C_capt_3 _p_E_range_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter vb va vc))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter vb va vc))) _p_E_range_match))) zenon_H7)) zenon_H5 zenon_H6)
) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(zenon_G
zenon_H4)) zenon_Hc)) _p_P_range_match_is_valid)) __C_1_1_2_2_6_LEMMA)))
).
Qed.

              Theorem __C_1_1_2_2_7_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter vb va vc))))).
              assert (__force_use_H122 := H122).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_2_7_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_2_7.
            Section __C_1_1_2_2_8.
(* File "vote.fcl", line 452, character 11, line 453, character 64 *)
Theorem for_zenon___C_1_1_2_2_8_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc va vb)) (_p_P_constr _p_C_capt_1
_p_E_range_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((~(Is_true (_p_V_consistency_rule v1 v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_range_match)))))))) vc (fun zenon_H19=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule vc v2)))
/\((~(Is_true (_p_V_consistency_rule vc v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vc v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_range_match))))))) va (fun zenon_H18=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule vc va)))/\((~(Is_true (
_p_V_consistency_rule vc v3)))/\(Is_true (_p_V_consistency_rule va v3)))
)->((Is_true (basics._equal_ _ (abst_value (abst_voter vc va v3)) va))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vc va v3)) (
_p_P_constr _p_C_capt_1 _p_E_range_match)))))) vb (fun zenon_H17=>(
zenon_imply _ _ (fun zenon_H16=>(zenon_notand _ _ (fun zenon_H15=>(
zenon_H15 (fun zenon_H12=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,((Is_true (_p_V_consistency_rule v1 v2))->(Is_true (
_p_V_consistency_rule v2 v1))))) vc (fun zenon_He=>(zenon_all _p_V_T (
fun v2:_p_V_T=>((Is_true (_p_V_consistency_rule vc v2))->(Is_true (
_p_V_consistency_rule v2 vc)))) va (fun zenon_H14=>(zenon_imply _ _ (
fun zenon_H13=>(zenon_H13 zenon_H12)) (fun zenon_H11=>(H12 zenon_H11))
zenon_H14)) zenon_He)) abst_consistency_rule_is_symmetric)))) (fun
zenon_H10=>(zenon_notand _ _ (fun zenon_Hf=>(zenon_Hf (fun zenon_Hb=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) vc (fun zenon_He=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule vc v2))->(Is_true (_p_V_consistency_rule v2 vc))))
 vb (fun zenon_Hd=>(zenon_imply _ _ (fun zenon_Hc=>(zenon_Hc zenon_Hb))
(fun zenon_Ha=>(H122 zenon_Ha)) zenon_Hd)) zenon_He))
abst_consistency_rule_is_symmetric)))) (fun zenon_H9=>(zenon_H9 H1))
zenon_H10)) zenon_H16)) (fun zenon_H8=>(zenon_and _ _ (fun zenon_H7
zenon_H6=>(zenon_G zenon_H6)) zenon_H8)) zenon_H17)) zenon_H18))
zenon_H19)) abst_vote_match_c1)))).
Qed.

              Theorem __C_1_1_2_2_8_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter vc va vb))
                            (_p_P_constr _p_C_capt_1 _p_E_range_match)))).
              assert (__force_use_H122 := H122).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_2_8_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_2_8.
            Section __C_1_1_2_2_9.
(* File "vote.fcl", line 455, characters 11-79 *)
Theorem for_zenon___C_1_1_2_2_9_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter vc va vb)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter vc va vb)) (_p_P_constr
_p_C_capt_1 _p_E_range_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_range_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter vc va vb)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_1 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 n2)) n2))) _p_E_range_match (fun zenon_H6=>(zenon_subst _ (
fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 _p_E_range_match)) _p_E_range_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter vc va vb))) _p_E_range_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_range_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vc
va vb))) _p_E_range_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_1
_p_E_range_match)) (_p_P_prj_b (abst_diag (abst_voter vc va vb))) (fun
zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter vc va vb)))))) (_p_P_constr
_p_C_capt_1 _p_E_range_match) (abst_diag (abst_voter vc va vb)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter vc va vb)) (_p_P_constr
_p_C_capt_1 _p_E_range_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter vc va vb))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter vc va vb))) _p_E_range_match))) zenon_H7)) zenon_H5 zenon_H6)
) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(zenon_G
zenon_H4)) zenon_Hc)) _p_P_range_match_is_valid)) __C_1_1_2_2_8_LEMMA)))
).
Qed.

              Theorem __C_1_1_2_2_9_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter vc va vb))))).
              assert (__force_use_H122 := H122).
              assert (__force_use_H12 := H12).
              assert (__force_use_H1 := H1).
              apply for_zenon___C_1_1_2_2_9_LEMMA;
              auto.
              Qed.
              End __C_1_1_2_2_9.
(* File "vote.fcl", line 457, character 19, line 460, character 39 *)
Theorem for_zenon___C_1_1_2_2_LEMMA:((abst_compatible (abst_voter va vb
vc) (abst_voter vb va vc))/\(abst_compatible (abst_voter va vb vc) (
abst_voter vc va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notand _ _ (fun zenon_H21=>(let zenon_H20
:=zenon_H21 in (zenon_notor _ _ (fun zenon_H1e zenon_H1f=>(zenon_notand
_ _ (fun zenon_H12=>(zenon_H12 __C_1_1_2_2_5_LEMMA)) (fun zenon_H1d=>(
zenon_notand _ _ (fun zenon_H1c=>(zenon_H1c __C_1_1_2_2_7_LEMMA)) (fun
zenon_H17=>(coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (
abst_value (abst_voter va vb vc)) va (fun zenon_Hd=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (abst_value (
abst_voter vb va vc)) vb (fun zenon_H19=>(zenon_subst _ (fun zenon_Vi=>(
Is_true zenon_Vi)) (_p_V_consistency_rule va vb) (_p_V_consistency_rule
(abst_value (abst_voter va vb vc)) (abst_value (abst_voter vb va vc))) (
fun zenon_H18=>(zenon_subst _ (fun zenon_Vk=>(~((_p_V_consistency_rule
zenon_Vk vb) = (_p_V_consistency_rule (abst_value (abst_voter va vb vc))
 (abst_value (abst_voter vb va vc)))))) va (abst_value (abst_voter va
vb vc)) (fun zenon_H1b=>(zenon_eqsym _ (abst_value (abst_voter va vb vc)
) va zenon_Hd zenon_H1b)) (zenon_subst _ (fun zenon_Vj=>(~((
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) zenon_Vj) = (
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vb va vc)))))) vb (abst_value (abst_voter vb va vc)) (fun
zenon_H1a=>(zenon_eqsym _ (abst_value (abst_voter vb va vc)) vb
zenon_H19 zenon_H1a)) (zenon_notnot _ (refl_equal (
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vb va vc)))))) zenon_H18)) zenon_H17 H1))
__C_1_1_2_2_2_LEMMA)) __C_1_1_2_2_1_LEMMA)) zenon_H1d)) zenon_H1e))
zenon_H20))) (fun zenon_H16=>(let zenon_H15:=zenon_H16 in (zenon_notor
_ _ (fun zenon_H13 zenon_H14=>(zenon_notand _ _ (fun zenon_H12=>(
zenon_H12 __C_1_1_2_2_5_LEMMA)) (fun zenon_H11=>(zenon_notand _ _ (fun
zenon_H10=>(zenon_H10 __C_1_1_2_2_9_LEMMA)) (fun zenon_H9=>(zenon_all
_p_V_T (fun a:_p_V_T=>(Is_true (_p_V_consistency_rule a a))) (
abst_value (abst_voter va vb vc)) (fun zenon_Ha=>(zenon_subst _ (fun
zenon_Vf=>(Is_true zenon_Vf)) (_p_V_consistency_rule (abst_value (
abst_voter va vb vc)) (abst_value (abst_voter va vb vc))) (
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vc va vb))) (fun zenon_Hb=>(zenon_subst _ (fun zenon_Vg=>(~((
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) zenon_Vg) = (
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vc va vb)))))) (abst_value (abst_voter va vb vc)) (
abst_value (abst_voter vc va vb)) (fun zenon_Hc=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (abst_value (
abst_voter va vb vc)) va (fun zenon_Hd=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (abst_value (
abst_voter vc va vb)) va (fun zenon_He=>(zenon_subst _ (fun zenon_Vh=>((
abst_value (abst_voter va vb vc)) = zenon_Vh)) va (abst_value (
abst_voter vc va vb)) (fun zenon_Hf=>(zenon_eqsym _ (abst_value (
abst_voter vc va vb)) va zenon_He zenon_Hf)) zenon_Hc zenon_Hd))
__C_1_1_2_2_3_LEMMA)) __C_1_1_2_2_1_LEMMA)) (zenon_notnot _ (refl_equal
(_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vc va vb))))) zenon_Hb)) zenon_H9 zenon_Ha))
_p_V_consistency_rule_reflexive)) zenon_H11)) zenon_H13)) zenon_H15)))
zenon_G)))).
Qed.

            Theorem __C_1_1_2_2_LEMMA :
              ((abst_compatible (abst_voter va vb vc) (abst_voter vb va vc)) /\
                 (abst_compatible (abst_voter va vb vc)
                   (abst_voter vc va vb))).
            assert (__force_use_H122 := H122).
            assert (__force_use_H12 := H12).
            assert (__force_use_H1 := H1).
            apply for_zenon___C_1_1_2_2_LEMMA;
            auto.
            Qed.
            End __C_1_1_2_2.
(* File "vote.fcl", line 462, characters 17-55 *)
Theorem for_zenon___C_1_1_2_LEMMA:((abst_compatible (abst_voter va vb
vc) (abst_voter vb va vc))/\(abst_compatible (abst_voter va vb vc) (
abst_voter vc va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_imply _ _ (fun zenon_H5=>(zenon_imply _ _ (
fun zenon_H6=>(zenon_H6 zenon_H5)) (fun zenon_H4=>(zenon_G zenon_H4))
__C_1_1_2_2_LEMMA)) (fun zenon_H4=>(zenon_G zenon_H4))
__C_1_1_2_1_LEMMA)))).
Qed.

          Theorem __C_1_1_2_LEMMA :
            ((abst_compatible (abst_voter va vb vc) (abst_voter vb va vc)) /\
               (abst_compatible (abst_voter va vb vc) (abst_voter vc va vb))).
          assert (__force_use_H12 := H12).
          assert (__force_use_H1 := H1).
          apply for_zenon___C_1_1_2_LEMMA;
          auto.
          Qed.
          End __C_1_1_2.
(* File "vote.fcl", line 464, characters 15-53 *)
Theorem for_zenon___C_1_1_LEMMA:((abst_compatible (abst_voter va vb vc)
(abst_voter vb va vc))/\(abst_compatible (abst_voter va vb vc) (
abst_voter vc va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_imply _ _ (fun zenon_H5=>(zenon_imply _ _ (
fun zenon_H6=>(zenon_H6 zenon_H5)) (fun zenon_H4=>(zenon_G zenon_H4))
__C_1_1_2_LEMMA)) (fun zenon_H4=>(zenon_G zenon_H4)) __C_1_1_1_LEMMA)))).
Qed.

        Theorem __C_1_1_LEMMA :
          ((abst_compatible (abst_voter va vb vc) (abst_voter vb va vc)) /\
             (abst_compatible (abst_voter va vb vc) (abst_voter vc va vb))).
        assert (__force_use_H1 := H1).
        apply for_zenon___C_1_1_LEMMA;
        auto.
        Qed.
        End __C_1_1.
      Section __C_1_2.
        Variable H2 : ~Is_true (((_p_V_consistency_rule va vb))).
        Section __C_1_2_1.
          Variable H21 : Is_true (((_p_V_consistency_rule va vc))).
          Section __C_1_2_1_1.
            Variable H211 : Is_true (((_p_V_consistency_rule vb vc))).
            Section __C_1_2_1_1_1.
              Section __C_1_2_1_1_1_1.
(* File "vote.fcl", line 486, characters 12-52 *)
Theorem for_zenon___C_1_2_1_1_1_1_LEMMA:((Is_true (
_p_V_consistency_rule vb va))->(Is_true (_p_V_consistency_rule va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notimply _ _ (fun zenon_H4 zenon_H3=>(
zenon_all _p_V_T (fun a:_p_V_T=>(forall b:_p_V_T,((Is_true (
_p_V_consistency_rule a b))->(Is_true (_p_V_consistency_rule b a)))))
vb (fun zenon_H7=>(zenon_all _p_V_T (fun b:_p_V_T=>((Is_true (
_p_V_consistency_rule vb b))->(Is_true (_p_V_consistency_rule b vb))))
va (fun zenon_H6=>(zenon_imply _ _ (fun zenon_H5=>(zenon_H5 zenon_H4)) (
fun zenon_H2=>(zenon_H3 zenon_H2)) zenon_H6)) zenon_H7))
_p_V_consistency_rule_symmetric)) zenon_G)))).
Qed.

                Theorem __C_1_2_1_1_1_1_LEMMA :
                  Is_true ((_p_V_consistency_rule vb va)) ->
                    Is_true ((_p_V_consistency_rule va vb)).
                assert (__force_use_H211 := H211).
                assert (__force_use_H21 := H21).
                assert (__force_use_H2 := H2).
                apply for_zenon___C_1_2_1_1_1_1_LEMMA;
                auto.
                Qed.
                End __C_1_2_1_1_1_1.
(* File "vote.fcl", line 487, characters 20-46 *)
Theorem for_zenon___C_1_2_1_1_1_LEMMA:(~(Is_true (_p_V_consistency_rule
vb va))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G (fun zenon_H4=>(zenon_imply _ _ (fun
zenon_H5=>(zenon_H5 zenon_H4)) (fun zenon_H3=>(H2 zenon_H3))
__C_1_2_1_1_1_1_LEMMA)))))).
Qed.

              Theorem __C_1_2_1_1_1_LEMMA :
                ~Is_true (((_p_V_consistency_rule vb va))).
              assert (__force_use_H211 := H211).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_1_1_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_1_1.
            Section __C_1_2_1_1_2.
(* File "vote.fcl", line 490, characters 11-63 *)
Theorem for_zenon___C_1_2_1_1_2_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vc)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((Is_true (_p_V_consistency_rule v1 v3))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_partial_match)))))))) va (fun zenon_H10=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule va v2)))
/\((Is_true (_p_V_consistency_rule va v3))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_partial_match))))))) vb (fun zenon_Hf=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule va vb)))/\((Is_true (
_p_V_consistency_rule va v3))/\(Is_true (_p_V_consistency_rule vb v3))))
->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) v3))/\(
Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_3 _p_E_partial_match)))))) vc (fun zenon_He=>(
zenon_imply _ _ (fun zenon_Hd=>(zenon_notand _ _ (fun zenon_Hc=>(
zenon_Hc (fun zenon_Hb=>(H2 zenon_Hb)))) (fun zenon_Ha=>(zenon_notand _
_ (fun zenon_H9=>(zenon_H9 H21)) (fun zenon_H8=>(zenon_H8 H211))
zenon_Ha)) zenon_Hd)) (fun zenon_H7=>(zenon_and _ _ (fun zenon_H5
zenon_H6=>(zenon_G zenon_H5)) zenon_H7)) zenon_He)) zenon_Hf))
zenon_H10)) abst_vote_partial_c3)))).
Qed.

              Theorem __C_1_2_1_1_2_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter va vb vc)) vc))).
              assert (__force_use_H211 := H211).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_1_2_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_1_2.
            Section __C_1_2_1_1_3.
(* File "vote.fcl", line 492, characters 11-69 *)
Theorem for_zenon___C_1_2_1_1_3_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter vb va vc)) vc)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((Is_true (_p_V_consistency_rule v1 v3))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_partial_match)))))))) vb (fun zenon_H10=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule vb v2)))
/\((Is_true (_p_V_consistency_rule vb v3))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vb v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_partial_match))))))) va (fun zenon_Hf=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule vb va)))/\((Is_true (
_p_V_consistency_rule vb v3))/\(Is_true (_p_V_consistency_rule va v3))))
->((Is_true (basics._equal_ _ (abst_value (abst_voter vb va v3)) v3))/\(
Is_true (basics._equal_ _ (abst_diag (abst_voter vb va v3)) (
_p_P_constr _p_C_capt_3 _p_E_partial_match)))))) vc (fun zenon_He=>(
zenon_imply _ _ (fun zenon_Hd=>(zenon_notand _ _ (fun zenon_Hc=>(
zenon_Hc (fun zenon_Hb=>(__C_1_2_1_1_1_LEMMA zenon_Hb)))) (fun
zenon_Ha=>(zenon_notand _ _ (fun zenon_H9=>(zenon_H9 H211)) (fun
zenon_H8=>(zenon_H8 H21)) zenon_Ha)) zenon_Hd)) (fun zenon_H7=>(
zenon_and _ _ (fun zenon_H5 zenon_H6=>(zenon_G zenon_H5)) zenon_H7))
zenon_He)) zenon_Hf)) zenon_H10)) abst_vote_partial_c3)))).
Qed.

              Theorem __C_1_2_1_1_3_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter vb va vc)) vc))).
              assert (__force_use_H211 := H211).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_1_3_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_1_3.
            Section __C_1_2_1_1_4.
(* File "vote.fcl", line 494, character 11, line 495, character 69 *)
Theorem for_zenon___C_1_2_1_1_4_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter vc va vb)) vc)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((
Is_true (_p_V_consistency_rule v1 v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v1))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_partial_match)))))))) vc (fun zenon_H19=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule vc v2))/\((
Is_true (_p_V_consistency_rule vc v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vc v2 v3)) vc))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_partial_match))))))) va (fun zenon_H18=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule vc va))/\((Is_true (
_p_V_consistency_rule vc v3))/\(~(Is_true (_p_V_consistency_rule va v3))
)))->((Is_true (basics._equal_ _ (abst_value (abst_voter vc va v3)) vc))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vc va v3)) (
_p_P_constr _p_C_capt_1 _p_E_partial_match)))))) vb (fun zenon_H17=>(
zenon_imply _ _ (fun zenon_H16=>(zenon_notand _ _ (fun zenon_H12=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) va (fun zenon_H15=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule va v2))->(Is_true (_p_V_consistency_rule v2 va))))
 vc (fun zenon_H14=>(zenon_imply _ _ (fun zenon_H13=>(zenon_H13 H21)) (
fun zenon_H11=>(zenon_H12 zenon_H11)) zenon_H14)) zenon_H15))
abst_consistency_rule_is_symmetric)) (fun zenon_H10=>(zenon_notand _ _ (
fun zenon_Hc=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((
Is_true (_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule
v2 v1))))) vb (fun zenon_Hf=>(zenon_all _p_V_T (fun v2:_p_V_T=>((
Is_true (_p_V_consistency_rule vb v2))->(Is_true (_p_V_consistency_rule
v2 vb)))) vc (fun zenon_He=>(zenon_imply _ _ (fun zenon_Hd=>(zenon_Hd
H211)) (fun zenon_Hb=>(zenon_Hc zenon_Hb)) zenon_He)) zenon_Hf))
abst_consistency_rule_is_symmetric)) (fun zenon_Ha=>(zenon_Ha (fun
zenon_H9=>(H2 zenon_H9)))) zenon_H10)) zenon_H16)) (fun zenon_H8=>(
zenon_and _ _ (fun zenon_H6 zenon_H7=>(zenon_G zenon_H6)) zenon_H8))
zenon_H17)) zenon_H18)) zenon_H19)) abst_vote_partial_c1)))).
Qed.

              Theorem __C_1_2_1_1_4_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter vc va vb)) vc))).
              assert (__force_use_H211 := H211).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_1_4_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_1_4.
            Section __C_1_2_1_1_5.
(* File "vote.fcl", line 498, characters 10-62 *)
Theorem for_zenon___C_1_2_1_1_5_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter va vb vc)) (_p_P_constr _p_C_capt_3
_p_E_partial_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((Is_true (_p_V_consistency_rule v1 v3))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_partial_match)))))))) va (fun zenon_H10=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule va v2)))
/\((Is_true (_p_V_consistency_rule va v3))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_partial_match))))))) vb (fun zenon_Hf=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule va vb)))/\((Is_true (
_p_V_consistency_rule va v3))/\(Is_true (_p_V_consistency_rule vb v3))))
->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) v3))/\(
Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_3 _p_E_partial_match)))))) vc (fun zenon_He=>(
zenon_imply _ _ (fun zenon_Hd=>(zenon_notand _ _ (fun zenon_Hc=>(
zenon_Hc (fun zenon_Hb=>(H2 zenon_Hb)))) (fun zenon_Ha=>(zenon_notand _
_ (fun zenon_H9=>(zenon_H9 H21)) (fun zenon_H8=>(zenon_H8 H211))
zenon_Ha)) zenon_Hd)) (fun zenon_H7=>(zenon_and _ _ (fun zenon_H6
zenon_H5=>(zenon_G zenon_H5)) zenon_H7)) zenon_He)) zenon_Hf))
zenon_H10)) abst_vote_partial_c3)))).
Qed.

              Theorem __C_1_2_1_1_5_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter va vb vc))
                            (_p_P_constr _p_C_capt_3 _p_E_partial_match)))).
              assert (__force_use_H211 := H211).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_1_5_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_1_5.
            Section __C_1_2_1_1_6.
(* File "vote.fcl", line 500, characters 11-81 *)
Theorem for_zenon___C_1_2_1_1_6_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter va vb vc)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter va vb vc)) (_p_P_constr
_p_C_capt_3 _p_E_partial_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_partial_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter va vb vc)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_3 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_3 n2)) n2))) _p_E_partial_match (fun zenon_H6=>(zenon_subst _
(fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_3 _p_E_partial_match)) _p_E_partial_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter va vb vc))) _p_E_partial_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_partial_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter va
vb vc))) _p_E_partial_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_3
_p_E_partial_match)) (_p_P_prj_b (abst_diag (abst_voter va vb vc))) (
fun zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter va vb vc)))))) (_p_P_constr
_p_C_capt_3 _p_E_partial_match) (abst_diag (abst_voter va vb vc)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter va vb vc)) (_p_P_constr
_p_C_capt_3 _p_E_partial_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter va vb vc))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter va vb vc))) _p_E_partial_match))) zenon_H7)) zenon_H5
zenon_H6)) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(
zenon_G zenon_H4)) zenon_Hc)) _p_P_partial_match_is_valid))
__C_1_2_1_1_5_LEMMA)))).
Qed.

              Theorem __C_1_2_1_1_6_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter va vb vc))))).
              assert (__force_use_H211 := H211).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_1_6_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_1_6.
            Section __C_1_2_1_1_7.
(* File "vote.fcl", line 504, characters 10-68 *)
Theorem for_zenon___C_1_2_1_1_7_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb va vc)) (_p_P_constr _p_C_capt_3
_p_E_partial_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((Is_true (_p_V_consistency_rule v1 v3))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_partial_match)))))))) vb (fun zenon_H10=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule vb v2)))
/\((Is_true (_p_V_consistency_rule vb v3))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vb v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_partial_match))))))) va (fun zenon_Hf=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule vb va)))/\((Is_true (
_p_V_consistency_rule vb v3))/\(Is_true (_p_V_consistency_rule va v3))))
->((Is_true (basics._equal_ _ (abst_value (abst_voter vb va v3)) v3))/\(
Is_true (basics._equal_ _ (abst_diag (abst_voter vb va v3)) (
_p_P_constr _p_C_capt_3 _p_E_partial_match)))))) vc (fun zenon_He=>(
zenon_imply _ _ (fun zenon_Hd=>(zenon_notand _ _ (fun zenon_Hc=>(
zenon_Hc (fun zenon_Hb=>(__C_1_2_1_1_1_LEMMA zenon_Hb)))) (fun
zenon_Ha=>(zenon_notand _ _ (fun zenon_H9=>(zenon_H9 H211)) (fun
zenon_H8=>(zenon_H8 H21)) zenon_Ha)) zenon_Hd)) (fun zenon_H7=>(
zenon_and _ _ (fun zenon_H6 zenon_H5=>(zenon_G zenon_H5)) zenon_H7))
zenon_He)) zenon_Hf)) zenon_H10)) abst_vote_partial_c3)))).
Qed.

              Theorem __C_1_2_1_1_7_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter vb va vc))
                            (_p_P_constr _p_C_capt_3 _p_E_partial_match)))).
              assert (__force_use_H211 := H211).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_1_7_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_1_7.
            Section __C_1_2_1_1_8.
(* File "vote.fcl", line 506, characters 10-80 *)
Theorem for_zenon___C_1_2_1_1_8_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter vb va vc)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter vb va vc)) (_p_P_constr
_p_C_capt_3 _p_E_partial_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_partial_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter vb va vc)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_3 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_3 n2)) n2))) _p_E_partial_match (fun zenon_H6=>(zenon_subst _
(fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_3 _p_E_partial_match)) _p_E_partial_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter vb va vc))) _p_E_partial_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_partial_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vb
va vc))) _p_E_partial_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_3
_p_E_partial_match)) (_p_P_prj_b (abst_diag (abst_voter vb va vc))) (
fun zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter vb va vc)))))) (_p_P_constr
_p_C_capt_3 _p_E_partial_match) (abst_diag (abst_voter vb va vc)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter vb va vc)) (_p_P_constr
_p_C_capt_3 _p_E_partial_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter vb va vc))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter vb va vc))) _p_E_partial_match))) zenon_H7)) zenon_H5
zenon_H6)) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(
zenon_G zenon_H4)) zenon_Hc)) _p_P_partial_match_is_valid))
__C_1_2_1_1_7_LEMMA)))).
Qed.

              Theorem __C_1_2_1_1_8_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter vb va vc))))).
              assert (__force_use_H211 := H211).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_1_8_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_1_8.
            Section __C_1_2_1_1_9.
(* File "vote.fcl", line 510, character 10, line 511, character 65 *)
Theorem for_zenon___C_1_2_1_1_9_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc va vb)) (_p_P_constr _p_C_capt_1
_p_E_partial_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((
Is_true (_p_V_consistency_rule v1 v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v1))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_partial_match)))))))) vc (fun zenon_H19=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule vc v2))/\((
Is_true (_p_V_consistency_rule vc v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vc v2 v3)) vc))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_partial_match))))))) va (fun zenon_H18=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule vc va))/\((Is_true (
_p_V_consistency_rule vc v3))/\(~(Is_true (_p_V_consistency_rule va v3))
)))->((Is_true (basics._equal_ _ (abst_value (abst_voter vc va v3)) vc))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vc va v3)) (
_p_P_constr _p_C_capt_1 _p_E_partial_match)))))) vb (fun zenon_H17=>(
zenon_imply _ _ (fun zenon_H16=>(zenon_notand _ _ (fun zenon_H12=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) va (fun zenon_H15=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule va v2))->(Is_true (_p_V_consistency_rule v2 va))))
 vc (fun zenon_H14=>(zenon_imply _ _ (fun zenon_H13=>(zenon_H13 H21)) (
fun zenon_H11=>(zenon_H12 zenon_H11)) zenon_H14)) zenon_H15))
abst_consistency_rule_is_symmetric)) (fun zenon_H10=>(zenon_notand _ _ (
fun zenon_Hc=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((
Is_true (_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule
v2 v1))))) vb (fun zenon_Hf=>(zenon_all _p_V_T (fun v2:_p_V_T=>((
Is_true (_p_V_consistency_rule vb v2))->(Is_true (_p_V_consistency_rule
v2 vb)))) vc (fun zenon_He=>(zenon_imply _ _ (fun zenon_Hd=>(zenon_Hd
H211)) (fun zenon_Hb=>(zenon_Hc zenon_Hb)) zenon_He)) zenon_Hf))
abst_consistency_rule_is_symmetric)) (fun zenon_Ha=>(zenon_Ha (fun
zenon_H9=>(H2 zenon_H9)))) zenon_H10)) zenon_H16)) (fun zenon_H8=>(
zenon_and _ _ (fun zenon_H7 zenon_H6=>(zenon_G zenon_H6)) zenon_H8))
zenon_H17)) zenon_H18)) zenon_H19)) abst_vote_partial_c1)))).
Qed.

              Theorem __C_1_2_1_1_9_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter vc va vb))
                            (_p_P_constr _p_C_capt_1 _p_E_partial_match)))).
              assert (__force_use_H211 := H211).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_1_9_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_1_9.
            Section __C_1_2_1_1_10.
(* File "vote.fcl", line 513, characters 10-80 *)
Theorem for_zenon___C_1_2_1_1_10_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter vc va vb)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter vc va vb)) (_p_P_constr
_p_C_capt_1 _p_E_partial_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_partial_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter vc va vb)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_1 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 n2)) n2))) _p_E_partial_match (fun zenon_H6=>(zenon_subst _
(fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 _p_E_partial_match)) _p_E_partial_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter vc va vb))) _p_E_partial_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_partial_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vc
va vb))) _p_E_partial_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_1
_p_E_partial_match)) (_p_P_prj_b (abst_diag (abst_voter vc va vb))) (
fun zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter vc va vb)))))) (_p_P_constr
_p_C_capt_1 _p_E_partial_match) (abst_diag (abst_voter vc va vb)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter vc va vb)) (_p_P_constr
_p_C_capt_1 _p_E_partial_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter vc va vb))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter vc va vb))) _p_E_partial_match))) zenon_H7)) zenon_H5
zenon_H6)) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(
zenon_G zenon_H4)) zenon_Hc)) _p_P_partial_match_is_valid))
__C_1_2_1_1_9_LEMMA)))).
Qed.

              Theorem __C_1_2_1_1_10_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter vc va vb))))).
              assert (__force_use_H211 := H211).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_1_10_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_1_10.
(* File "vote.fcl", line 515, character 18, line 517, character 35 *)
Theorem for_zenon___C_1_2_1_1_LEMMA:((abst_compatible (abst_voter va vb
vc) (abst_voter vb va vc))/\(abst_compatible (abst_voter va vb vc) (
abst_voter vc va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notand _ _ (fun zenon_H20=>(let zenon_H1f
:=zenon_H20 in (zenon_notor _ _ (fun zenon_H1d zenon_H1e=>(zenon_notand
_ _ (fun zenon_H11=>(zenon_H11 __C_1_2_1_1_6_LEMMA)) (fun zenon_H1c=>(
zenon_notand _ _ (fun zenon_H1b=>(zenon_H1b __C_1_2_1_1_8_LEMMA)) (fun
zenon_H16=>(zenon_all _p_V_T (fun a:_p_V_T=>(Is_true (
_p_V_consistency_rule a a))) (abst_value (abst_voter va vb vc)) (fun
zenon_H9=>(zenon_subst _ (fun zenon_Vi=>(Is_true zenon_Vi)) (
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter va vb vc))) (_p_V_consistency_rule (abst_value (abst_voter
va vb vc)) (abst_value (abst_voter vb va vc))) (fun zenon_H17=>(
zenon_subst _ (fun zenon_Vj=>(~((_p_V_consistency_rule (abst_value (
abst_voter va vb vc)) zenon_Vj) = (_p_V_consistency_rule (abst_value (
abst_voter va vb vc)) (abst_value (abst_voter vb va vc)))))) (
abst_value (abst_voter va vb vc)) (abst_value (abst_voter vb va vc)) (
fun zenon_H18=>(coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (
abst_value (abst_voter va vb vc)) vc (fun zenon_Hc=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (abst_value (
abst_voter vb va vc)) vc (fun zenon_H19=>(zenon_subst _ (fun zenon_Vk=>(
(abst_value (abst_voter va vb vc)) = zenon_Vk)) vc (abst_value (
abst_voter vb va vc)) (fun zenon_H1a=>(zenon_eqsym _ (abst_value (
abst_voter vb va vc)) vc zenon_H19 zenon_H1a)) zenon_H18 zenon_Hc))
__C_1_2_1_1_3_LEMMA)) __C_1_2_1_1_2_LEMMA)) (zenon_notnot _ (refl_equal
(_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vb va vc))))) zenon_H17)) zenon_H16 zenon_H9))
_p_V_consistency_rule_reflexive)) zenon_H1c)) zenon_H1d)) zenon_H1f))) (
fun zenon_H15=>(let zenon_H14:=zenon_H15 in (zenon_notor _ _ (fun
zenon_H12 zenon_H13=>(zenon_notand _ _ (fun zenon_H11=>(zenon_H11
__C_1_2_1_1_6_LEMMA)) (fun zenon_H10=>(zenon_notand _ _ (fun zenon_Hf=>(
zenon_Hf __C_1_2_1_1_10_LEMMA)) (fun zenon_H8=>(zenon_all _p_V_T (fun a
:_p_V_T=>(Is_true (_p_V_consistency_rule a a))) (abst_value (abst_voter
va vb vc)) (fun zenon_H9=>(zenon_subst _ (fun zenon_Vf=>(Is_true
zenon_Vf)) (_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (
abst_value (abst_voter va vb vc))) (_p_V_consistency_rule (abst_value (
abst_voter va vb vc)) (abst_value (abst_voter vc va vb))) (fun
zenon_Ha=>(zenon_subst _ (fun zenon_Vg=>(~((_p_V_consistency_rule (
abst_value (abst_voter va vb vc)) zenon_Vg) = (_p_V_consistency_rule (
abst_value (abst_voter va vb vc)) (abst_value (abst_voter vc va vb))))))
 (abst_value (abst_voter va vb vc)) (abst_value (abst_voter vc va vb)) (
fun zenon_Hb=>(coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (
abst_value (abst_voter va vb vc)) vc (fun zenon_Hc=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (abst_value (
abst_voter vc va vb)) vc (fun zenon_Hd=>(zenon_subst _ (fun zenon_Vh=>((
abst_value (abst_voter va vb vc)) = zenon_Vh)) vc (abst_value (
abst_voter vc va vb)) (fun zenon_He=>(zenon_eqsym _ (abst_value (
abst_voter vc va vb)) vc zenon_Hd zenon_He)) zenon_Hb zenon_Hc))
__C_1_2_1_1_4_LEMMA)) __C_1_2_1_1_2_LEMMA)) (zenon_notnot _ (refl_equal
(_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vc va vb))))) zenon_Ha)) zenon_H8 zenon_H9))
_p_V_consistency_rule_reflexive)) zenon_H10)) zenon_H12)) zenon_H14)))
zenon_G)))).
Qed.

            Theorem __C_1_2_1_1_LEMMA :
              ((abst_compatible (abst_voter va vb vc) (abst_voter vb va vc)) /\
                 (abst_compatible (abst_voter va vb vc)
                   (abst_voter vc va vb))).
            assert (__force_use_H211 := H211).
            assert (__force_use_H21 := H21).
            assert (__force_use_H2 := H2).
            apply for_zenon___C_1_2_1_1_LEMMA;
            auto.
            Qed.
            End __C_1_2_1_1.
          Section __C_1_2_1_2.
            Variable H212 : ~Is_true (((_p_V_consistency_rule vb vc))).
            Section __C_1_2_1_2_1.
              Section __C_1_2_1_2_1_1.
(* File "vote.fcl", line 527, characters 12-52 *)
Theorem for_zenon___C_1_2_1_2_1_1_LEMMA:((Is_true (
_p_V_consistency_rule vb va))->(Is_true (_p_V_consistency_rule va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notimply _ _ (fun zenon_H4 zenon_H3=>(
zenon_all _p_V_T (fun a:_p_V_T=>(forall b:_p_V_T,((Is_true (
_p_V_consistency_rule a b))->(Is_true (_p_V_consistency_rule b a)))))
vb (fun zenon_H7=>(zenon_all _p_V_T (fun b:_p_V_T=>((Is_true (
_p_V_consistency_rule vb b))->(Is_true (_p_V_consistency_rule b vb))))
va (fun zenon_H6=>(zenon_imply _ _ (fun zenon_H5=>(zenon_H5 zenon_H4)) (
fun zenon_H2=>(zenon_H3 zenon_H2)) zenon_H6)) zenon_H7))
_p_V_consistency_rule_symmetric)) zenon_G)))).
Qed.

                Theorem __C_1_2_1_2_1_1_LEMMA :
                  Is_true ((_p_V_consistency_rule vb va)) ->
                    Is_true ((_p_V_consistency_rule va vb)).
                assert (__force_use_H212 := H212).
                assert (__force_use_H21 := H21).
                assert (__force_use_H2 := H2).
                apply for_zenon___C_1_2_1_2_1_1_LEMMA;
                auto.
                Qed.
                End __C_1_2_1_2_1_1.
(* File "vote.fcl", line 528, characters 20-46 *)
Theorem for_zenon___C_1_2_1_2_1_LEMMA:(~(Is_true (_p_V_consistency_rule
vb va))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G (fun zenon_H4=>(zenon_imply _ _ (fun
zenon_H5=>(zenon_H5 zenon_H4)) (fun zenon_H3=>(H2 zenon_H3))
__C_1_2_1_2_1_1_LEMMA)))))).
Qed.

              Theorem __C_1_2_1_2_1_LEMMA :
                ~Is_true (((_p_V_consistency_rule vb va))).
              assert (__force_use_H212 := H212).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_2_1_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_2_1.
            Section __C_1_2_1_2_2.
(* File "vote.fcl", line 530, characters 11-61 *)
Theorem for_zenon___C_1_2_1_2_2_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vc)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((Is_true (_p_V_consistency_rule v1 v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_range_match)))))))) va (fun zenon_H11=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule va v2)))
/\((Is_true (_p_V_consistency_rule va v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_range_match))))))) vb (fun zenon_H10=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule va vb)))/\((Is_true (
_p_V_consistency_rule va v3))/\(~(Is_true (_p_V_consistency_rule vb v3))
)))->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) v3))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_2 _p_E_range_match)))))) vc (fun zenon_Hf=>(
zenon_imply _ _ (fun zenon_He=>(zenon_notand _ _ (fun zenon_Hd=>(
zenon_Hd (fun zenon_Hc=>(H2 zenon_Hc)))) (fun zenon_Hb=>(zenon_notand _
_ (fun zenon_Ha=>(zenon_Ha H21)) (fun zenon_H9=>(zenon_H9 (fun
zenon_H8=>(H212 zenon_H8)))) zenon_Hb)) zenon_He)) (fun zenon_H7=>(
zenon_and _ _ (fun zenon_H5 zenon_H6=>(zenon_G zenon_H5)) zenon_H7))
zenon_Hf)) zenon_H10)) zenon_H11)) abst_vote_match_c2)))).
Qed.

              Theorem __C_1_2_1_2_2_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter va vb vc)) vc))).
              assert (__force_use_H212 := H212).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_2_2_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_2_2.
            Section __C_1_2_1_2_3.
(* File "vote.fcl", line 532, characters 11-67 *)
Theorem for_zenon___C_1_2_1_2_3_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter vb va vc)) va)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((~(Is_true (_p_V_consistency_rule v1 v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_range_match)))))))) vb (fun zenon_H11=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule vb v2)))
/\((~(Is_true (_p_V_consistency_rule vb v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vb v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_range_match))))))) va (fun zenon_H10=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule vb va)))/\((~(Is_true (
_p_V_consistency_rule vb v3)))/\(Is_true (_p_V_consistency_rule va v3)))
)->((Is_true (basics._equal_ _ (abst_value (abst_voter vb va v3)) va))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vb va v3)) (
_p_P_constr _p_C_capt_1 _p_E_range_match)))))) vc (fun zenon_Hf=>(
zenon_imply _ _ (fun zenon_He=>(zenon_notand _ _ (fun zenon_Hd=>(
zenon_Hd (fun zenon_Hc=>(__C_1_2_1_2_1_LEMMA zenon_Hc)))) (fun
zenon_Hb=>(zenon_notand _ _ (fun zenon_Ha=>(zenon_Ha (fun zenon_H9=>(
H212 zenon_H9)))) (fun zenon_H8=>(zenon_H8 H21)) zenon_Hb)) zenon_He)) (
fun zenon_H7=>(zenon_and _ _ (fun zenon_H5 zenon_H6=>(zenon_G zenon_H5))
 zenon_H7)) zenon_Hf)) zenon_H10)) zenon_H11)) abst_vote_match_c1)))).
Qed.

              Theorem __C_1_2_1_2_3_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter vb va vc)) va))).
              assert (__force_use_H212 := H212).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_2_3_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_2_3.
            Section __C_1_2_1_2_4.
              Section __C_1_2_1_2_4_1.
(* File "vote.fcl", line 535, characters 12-52 *)
Theorem for_zenon___C_1_2_1_2_4_1_LEMMA:((Is_true (
_p_V_consistency_rule vc vb))->(Is_true (_p_V_consistency_rule vb vc))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notimply _ _ (fun zenon_H4 zenon_H3=>(
zenon_all _p_V_T (fun a:_p_V_T=>(forall b:_p_V_T,((Is_true (
_p_V_consistency_rule a b))->(Is_true (_p_V_consistency_rule b a)))))
vc (fun zenon_H7=>(zenon_all _p_V_T (fun b:_p_V_T=>((Is_true (
_p_V_consistency_rule vc b))->(Is_true (_p_V_consistency_rule b vc))))
vb (fun zenon_H6=>(zenon_imply _ _ (fun zenon_H5=>(zenon_H5 zenon_H4)) (
fun zenon_H2=>(zenon_H3 zenon_H2)) zenon_H6)) zenon_H7))
_p_V_consistency_rule_symmetric)) zenon_G)))).
Qed.

                Theorem __C_1_2_1_2_4_1_LEMMA :
                  Is_true ((_p_V_consistency_rule vc vb)) ->
                    Is_true ((_p_V_consistency_rule vb vc)).
                assert (__force_use_H212 := H212).
                assert (__force_use_H21 := H21).
                assert (__force_use_H2 := H2).
                apply for_zenon___C_1_2_1_2_4_1_LEMMA;
                auto.
                Qed.
                End __C_1_2_1_2_4_1.
(* File "vote.fcl", line 536, characters 20-48 *)
Theorem for_zenon___C_1_2_1_2_4_LEMMA:(~(Is_true (_p_V_consistency_rule
vc vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G (fun zenon_H4=>(zenon_imply _ _ (fun
zenon_H5=>(zenon_H5 zenon_H4)) (fun zenon_H3=>(H212 zenon_H3))
__C_1_2_1_2_4_1_LEMMA)))))).
Qed.

              Theorem __C_1_2_1_2_4_LEMMA :
                ~Is_true (((_p_V_consistency_rule vc vb))).
              assert (__force_use_H212 := H212).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_2_4_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_2_4.
            Section __C_1_2_1_2_5.
(* File "vote.fcl", line 538, character 11, line 539, character 67 *)
Theorem for_zenon___C_1_2_1_2_5_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter vc va vb)) vc)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((~
(Is_true (_p_V_consistency_rule v1 v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v1))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_range_match)))))))) vc (fun zenon_H16=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule vc v2))/\((
~(Is_true (_p_V_consistency_rule vc v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vc v2 v3)) vc))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_range_match))))))) va (fun zenon_H15=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule vc va))/\((~(Is_true (
_p_V_consistency_rule vc v3)))/\(~(Is_true (_p_V_consistency_rule va v3)
))))->((Is_true (basics._equal_ _ (abst_value (abst_voter vc va v3)) vc)
)/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vc va v3)) (
_p_P_constr _p_C_capt_3 _p_E_range_match)))))) vb (fun zenon_H14=>(
zenon_imply _ _ (fun zenon_H13=>(zenon_notand _ _ (fun zenon_Hf=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) va (fun zenon_H12=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule va v2))->(Is_true (_p_V_consistency_rule v2 va))))
 vc (fun zenon_H11=>(zenon_imply _ _ (fun zenon_H10=>(zenon_H10 H21)) (
fun zenon_He=>(zenon_Hf zenon_He)) zenon_H11)) zenon_H12))
abst_consistency_rule_is_symmetric)) (fun zenon_Hd=>(zenon_notand _ _ (
fun zenon_Hc=>(zenon_Hc (fun zenon_Hb=>(__C_1_2_1_2_4_LEMMA zenon_Hb))))
 (fun zenon_Ha=>(zenon_Ha (fun zenon_H9=>(H2 zenon_H9)))) zenon_Hd))
zenon_H13)) (fun zenon_H8=>(zenon_and _ _ (fun zenon_H6 zenon_H7=>(
zenon_G zenon_H6)) zenon_H8)) zenon_H14)) zenon_H15)) zenon_H16))
abst_vote_match_c3)))).
Qed.

              Theorem __C_1_2_1_2_5_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter vc va vb)) vc))).
              assert (__force_use_H212 := H212).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_2_5_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_2_5.
            Section __C_1_2_1_2_6.
(* File "vote.fcl", line 543, characters 11-61 *)
Theorem for_zenon___C_1_2_1_2_6_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter va vb vc)) (_p_P_constr _p_C_capt_2
_p_E_range_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((Is_true (_p_V_consistency_rule v1 v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_range_match)))))))) va (fun zenon_H11=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule va v2)))
/\((Is_true (_p_V_consistency_rule va v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_range_match))))))) vb (fun zenon_H10=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule va vb)))/\((Is_true (
_p_V_consistency_rule va v3))/\(~(Is_true (_p_V_consistency_rule vb v3))
)))->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) v3))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_2 _p_E_range_match)))))) vc (fun zenon_Hf=>(
zenon_imply _ _ (fun zenon_He=>(zenon_notand _ _ (fun zenon_Hd=>(
zenon_Hd (fun zenon_Hc=>(H2 zenon_Hc)))) (fun zenon_Hb=>(zenon_notand _
_ (fun zenon_Ha=>(zenon_Ha H21)) (fun zenon_H9=>(zenon_H9 (fun
zenon_H8=>(H212 zenon_H8)))) zenon_Hb)) zenon_He)) (fun zenon_H7=>(
zenon_and _ _ (fun zenon_H6 zenon_H5=>(zenon_G zenon_H5)) zenon_H7))
zenon_Hf)) zenon_H10)) zenon_H11)) abst_vote_match_c2)))).
Qed.

              Theorem __C_1_2_1_2_6_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter va vb vc))
                            (_p_P_constr _p_C_capt_2 _p_E_range_match)))).
              assert (__force_use_H212 := H212).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_2_6_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_2_6.
            Section __C_1_2_1_2_7.
(* File "vote.fcl", line 545, characters 11-79 *)
Theorem for_zenon___C_1_2_1_2_7_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter va vb vc)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter va vb vc)) (_p_P_constr
_p_C_capt_2 _p_E_range_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_range_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter va vb vc)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_2 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_2 n2)) n2))) _p_E_range_match (fun zenon_H6=>(zenon_subst _ (
fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_2 _p_E_range_match)) _p_E_range_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter va vb vc))) _p_E_range_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_range_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter va
vb vc))) _p_E_range_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_2
_p_E_range_match)) (_p_P_prj_b (abst_diag (abst_voter va vb vc))) (fun
zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter va vb vc)))))) (_p_P_constr
_p_C_capt_2 _p_E_range_match) (abst_diag (abst_voter va vb vc)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter va vb vc)) (_p_P_constr
_p_C_capt_2 _p_E_range_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter va vb vc))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter va vb vc))) _p_E_range_match))) zenon_H7)) zenon_H5 zenon_H6)
) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(zenon_G
zenon_H4)) zenon_Hc)) _p_P_range_match_is_valid)) __C_1_2_1_2_6_LEMMA)))
).
Qed.

              Theorem __C_1_2_1_2_7_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter va vb vc))))).
              assert (__force_use_H212 := H212).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_2_7_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_2_7.
            Section __C_1_2_1_2_8.
(* File "vote.fcl", line 549, characters 10-66 *)
Theorem for_zenon___C_1_2_1_2_8_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb va vc)) (_p_P_constr _p_C_capt_1
_p_E_range_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((~(Is_true (_p_V_consistency_rule v1 v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_range_match)))))))) vb (fun zenon_H11=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule vb v2)))
/\((~(Is_true (_p_V_consistency_rule vb v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vb v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_range_match))))))) va (fun zenon_H10=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule vb va)))/\((~(Is_true (
_p_V_consistency_rule vb v3)))/\(Is_true (_p_V_consistency_rule va v3)))
)->((Is_true (basics._equal_ _ (abst_value (abst_voter vb va v3)) va))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vb va v3)) (
_p_P_constr _p_C_capt_1 _p_E_range_match)))))) vc (fun zenon_Hf=>(
zenon_imply _ _ (fun zenon_He=>(zenon_notand _ _ (fun zenon_Hd=>(
zenon_Hd (fun zenon_Hc=>(__C_1_2_1_2_1_LEMMA zenon_Hc)))) (fun
zenon_Hb=>(zenon_notand _ _ (fun zenon_Ha=>(zenon_Ha (fun zenon_H9=>(
H212 zenon_H9)))) (fun zenon_H8=>(zenon_H8 H21)) zenon_Hb)) zenon_He)) (
fun zenon_H7=>(zenon_and _ _ (fun zenon_H6 zenon_H5=>(zenon_G zenon_H5))
 zenon_H7)) zenon_Hf)) zenon_H10)) zenon_H11)) abst_vote_match_c1)))).
Qed.

              Theorem __C_1_2_1_2_8_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter vb va vc))
                            (_p_P_constr _p_C_capt_1 _p_E_range_match)))).
              assert (__force_use_H212 := H212).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_2_8_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_2_8.
            Section __C_1_2_1_2_9.
(* File "vote.fcl", line 551, characters 10-78 *)
Theorem for_zenon___C_1_2_1_2_9_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter vb va vc)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter vb va vc)) (_p_P_constr
_p_C_capt_1 _p_E_range_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_range_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter vb va vc)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_1 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 n2)) n2))) _p_E_range_match (fun zenon_H6=>(zenon_subst _ (
fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 _p_E_range_match)) _p_E_range_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter vb va vc))) _p_E_range_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_range_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vb
va vc))) _p_E_range_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_1
_p_E_range_match)) (_p_P_prj_b (abst_diag (abst_voter vb va vc))) (fun
zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter vb va vc)))))) (_p_P_constr
_p_C_capt_1 _p_E_range_match) (abst_diag (abst_voter vb va vc)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter vb va vc)) (_p_P_constr
_p_C_capt_1 _p_E_range_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter vb va vc))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter vb va vc))) _p_E_range_match))) zenon_H7)) zenon_H5 zenon_H6)
) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(zenon_G
zenon_H4)) zenon_Hc)) _p_P_range_match_is_valid)) __C_1_2_1_2_8_LEMMA)))
).
Qed.

              Theorem __C_1_2_1_2_9_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter vb va vc))))).
              assert (__force_use_H212 := H212).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_2_9_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_2_9.
            Section __C_1_2_1_2_10.
(* File "vote.fcl", line 555, character 10, line 556, character 63 *)
Theorem for_zenon___C_1_2_1_2_10_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc va vb)) (_p_P_constr _p_C_capt_3
_p_E_range_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((~
(Is_true (_p_V_consistency_rule v1 v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v1))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_range_match)))))))) vc (fun zenon_H16=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule vc v2))/\((
~(Is_true (_p_V_consistency_rule vc v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vc v2 v3)) vc))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_range_match))))))) va (fun zenon_H15=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule vc va))/\((~(Is_true (
_p_V_consistency_rule vc v3)))/\(~(Is_true (_p_V_consistency_rule va v3)
))))->((Is_true (basics._equal_ _ (abst_value (abst_voter vc va v3)) vc)
)/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vc va v3)) (
_p_P_constr _p_C_capt_3 _p_E_range_match)))))) vb (fun zenon_H14=>(
zenon_imply _ _ (fun zenon_H13=>(zenon_notand _ _ (fun zenon_Hf=>(
zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2:_p_V_T,((Is_true (
_p_V_consistency_rule v1 v2))->(Is_true (_p_V_consistency_rule v2 v1))))
) va (fun zenon_H12=>(zenon_all _p_V_T (fun v2:_p_V_T=>((Is_true (
_p_V_consistency_rule va v2))->(Is_true (_p_V_consistency_rule v2 va))))
 vc (fun zenon_H11=>(zenon_imply _ _ (fun zenon_H10=>(zenon_H10 H21)) (
fun zenon_He=>(zenon_Hf zenon_He)) zenon_H11)) zenon_H12))
abst_consistency_rule_is_symmetric)) (fun zenon_Hd=>(zenon_notand _ _ (
fun zenon_Hc=>(zenon_Hc (fun zenon_Hb=>(__C_1_2_1_2_4_LEMMA zenon_Hb))))
 (fun zenon_Ha=>(zenon_Ha (fun zenon_H9=>(H2 zenon_H9)))) zenon_Hd))
zenon_H13)) (fun zenon_H8=>(zenon_and _ _ (fun zenon_H7 zenon_H6=>(
zenon_G zenon_H6)) zenon_H8)) zenon_H14)) zenon_H15)) zenon_H16))
abst_vote_match_c3)))).
Qed.

              Theorem __C_1_2_1_2_10_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter vc va vb))
                            (_p_P_constr _p_C_capt_3 _p_E_range_match)))).
              assert (__force_use_H212 := H212).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_2_10_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_2_10.
            Section __C_1_2_1_2_11.
(* File "vote.fcl", line 558, characters 10-79 *)
Theorem for_zenon___C_1_2_1_2_11_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter vc va vb)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter vc va vb)) (_p_P_constr
_p_C_capt_3 _p_E_range_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_range_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter vc va vb)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_3 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_3 n2)) n2))) _p_E_range_match (fun zenon_H6=>(zenon_subst _ (
fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_3 _p_E_range_match)) _p_E_range_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter vc va vb))) _p_E_range_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_range_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vc
va vb))) _p_E_range_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_3
_p_E_range_match)) (_p_P_prj_b (abst_diag (abst_voter vc va vb))) (fun
zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter vc va vb)))))) (_p_P_constr
_p_C_capt_3 _p_E_range_match) (abst_diag (abst_voter vc va vb)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter vc va vb)) (_p_P_constr
_p_C_capt_3 _p_E_range_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter vc va vb))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter vc va vb))) _p_E_range_match))) zenon_H7)) zenon_H5 zenon_H6)
) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(zenon_G
zenon_H4)) zenon_Hc)) _p_P_range_match_is_valid)) __C_1_2_1_2_10_LEMMA))
)).
Qed.

              Theorem __C_1_2_1_2_11_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter vc va vb))))).
              assert (__force_use_H212 := H212).
              assert (__force_use_H21 := H21).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_1_2_11_LEMMA;
              auto.
              Qed.
              End __C_1_2_1_2_11.
(* File "vote.fcl", line 561, character 18, line 564, character 33 *)
Theorem for_zenon___C_1_2_1_2_LEMMA:((abst_compatible (abst_voter va vb
vc) (abst_voter vb va vc))/\(abst_compatible (abst_voter va vb vc) (
abst_voter vc va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notand _ _ (fun zenon_H26=>(let zenon_H25
:=zenon_H26 in (zenon_notor _ _ (fun zenon_H23 zenon_H24=>(zenon_notand
_ _ (fun zenon_H13=>(zenon_H13 __C_1_2_1_2_7_LEMMA)) (fun zenon_H22=>(
zenon_notand _ _ (fun zenon_H21=>(zenon_H21 __C_1_2_1_2_9_LEMMA)) (fun
zenon_H18=>(coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (
abst_value (abst_voter va vb vc)) vc (fun zenon_He=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (abst_value (
abst_voter vb va vc)) va (fun zenon_H1b=>(zenon_all _p_V_T (fun v1
:_p_V_T=>(forall v2:_p_V_T,((Is_true (_p_V_consistency_rule v1 v2))->(
Is_true (_p_V_consistency_rule v2 v1))))) va (fun zenon_H20=>(zenon_all
_p_V_T (fun v2:_p_V_T=>((Is_true (_p_V_consistency_rule va v2))->(
Is_true (_p_V_consistency_rule v2 va)))) vc (fun zenon_H1f=>(
zenon_imply _ _ (fun zenon_H1e=>(zenon_H1e H21)) (fun zenon_H19=>(
zenon_subst _ (fun zenon_Vi=>(Is_true zenon_Vi)) (_p_V_consistency_rule
vc va) (_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (
abst_value (abst_voter vb va vc))) (fun zenon_H1a=>(zenon_subst _ (fun
zenon_Vk=>(~((_p_V_consistency_rule zenon_Vk va) = (
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vb va vc)))))) vc (abst_value (abst_voter va vb vc)) (fun
zenon_H1d=>(zenon_eqsym _ (abst_value (abst_voter va vb vc)) vc
zenon_He zenon_H1d)) (zenon_subst _ (fun zenon_Vj=>(~((
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) zenon_Vj) = (
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vb va vc)))))) va (abst_value (abst_voter vb va vc)) (fun
zenon_H1c=>(zenon_eqsym _ (abst_value (abst_voter vb va vc)) va
zenon_H1b zenon_H1c)) (zenon_notnot _ (refl_equal (
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vb va vc)))))) zenon_H1a)) zenon_H18 zenon_H19)) zenon_H1f))
zenon_H20)) abst_consistency_rule_is_symmetric)) __C_1_2_1_2_3_LEMMA))
__C_1_2_1_2_2_LEMMA)) zenon_H22)) zenon_H23)) zenon_H25))) (fun
zenon_H17=>(let zenon_H16:=zenon_H17 in (zenon_notor _ _ (fun zenon_H14
zenon_H15=>(zenon_notand _ _ (fun zenon_H13=>(zenon_H13
__C_1_2_1_2_7_LEMMA)) (fun zenon_H12=>(zenon_notand _ _ (fun zenon_H11=>
(zenon_H11 __C_1_2_1_2_11_LEMMA)) (fun zenon_Ha=>(zenon_all _p_V_T (fun
a:_p_V_T=>(Is_true (_p_V_consistency_rule a a))) (abst_value (
abst_voter va vb vc)) (fun zenon_Hb=>(zenon_subst _ (fun zenon_Vf=>(
Is_true zenon_Vf)) (_p_V_consistency_rule (abst_value (abst_voter va vb
vc)) (abst_value (abst_voter va vb vc))) (_p_V_consistency_rule (
abst_value (abst_voter va vb vc)) (abst_value (abst_voter vc va vb))) (
fun zenon_Hc=>(zenon_subst _ (fun zenon_Vg=>(~((_p_V_consistency_rule (
abst_value (abst_voter va vb vc)) zenon_Vg) = (_p_V_consistency_rule (
abst_value (abst_voter va vb vc)) (abst_value (abst_voter vc va vb))))))
 (abst_value (abst_voter va vb vc)) (abst_value (abst_voter vc va vb)) (
fun zenon_Hd=>(coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (
abst_value (abst_voter va vb vc)) vc (fun zenon_He=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (abst_value (
abst_voter vc va vb)) vc (fun zenon_Hf=>(zenon_subst _ (fun zenon_Vh=>((
abst_value (abst_voter va vb vc)) = zenon_Vh)) vc (abst_value (
abst_voter vc va vb)) (fun zenon_H10=>(zenon_eqsym _ (abst_value (
abst_voter vc va vb)) vc zenon_Hf zenon_H10)) zenon_Hd zenon_He))
__C_1_2_1_2_5_LEMMA)) __C_1_2_1_2_2_LEMMA)) (zenon_notnot _ (refl_equal
(_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vc va vb))))) zenon_Hc)) zenon_Ha zenon_Hb))
_p_V_consistency_rule_reflexive)) zenon_H12)) zenon_H14)) zenon_H16)))
zenon_G)))).
Qed.

            Theorem __C_1_2_1_2_LEMMA :
              ((abst_compatible (abst_voter va vb vc) (abst_voter vb va vc)) /\
                 (abst_compatible (abst_voter va vb vc)
                   (abst_voter vc va vb))).
            assert (__force_use_H212 := H212).
            assert (__force_use_H21 := H21).
            assert (__force_use_H2 := H2).
            apply for_zenon___C_1_2_1_2_LEMMA;
            auto.
            Qed.
            End __C_1_2_1_2.
(* File "vote.fcl", line 566, characters 17-55 *)
Theorem for_zenon___C_1_2_1_LEMMA:((abst_compatible (abst_voter va vb
vc) (abst_voter vb va vc))/\(abst_compatible (abst_voter va vb vc) (
abst_voter vc va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_imply _ _ (fun zenon_H5=>(zenon_imply _ _ (
fun zenon_H6=>(zenon_H6 zenon_H5)) (fun zenon_H4=>(zenon_G zenon_H4))
__C_1_2_1_2_LEMMA)) (fun zenon_H4=>(zenon_G zenon_H4))
__C_1_2_1_1_LEMMA)))).
Qed.

          Theorem __C_1_2_1_LEMMA :
            ((abst_compatible (abst_voter va vb vc) (abst_voter vb va vc)) /\
               (abst_compatible (abst_voter va vb vc) (abst_voter vc va vb))).
          assert (__force_use_H21 := H21).
          assert (__force_use_H2 := H2).
          apply for_zenon___C_1_2_1_LEMMA;
          auto.
          Qed.
          End __C_1_2_1.
        Section __C_1_2_2.
          Variable H22 : ~Is_true (((_p_V_consistency_rule va vc))).
          Section __C_1_2_2_1.
            Variable H221 : Is_true (((_p_V_consistency_rule vb vc))).
            Section __C_1_2_2_1_1.
              Section __C_1_2_2_1_1_1.
(* File "vote.fcl", line 584, characters 12-52 *)
Theorem for_zenon___C_1_2_2_1_1_1_LEMMA:((Is_true (
_p_V_consistency_rule vb va))->(Is_true (_p_V_consistency_rule va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notimply _ _ (fun zenon_H4 zenon_H3=>(
zenon_all _p_V_T (fun a:_p_V_T=>(forall b:_p_V_T,((Is_true (
_p_V_consistency_rule a b))->(Is_true (_p_V_consistency_rule b a)))))
vb (fun zenon_H7=>(zenon_all _p_V_T (fun b:_p_V_T=>((Is_true (
_p_V_consistency_rule vb b))->(Is_true (_p_V_consistency_rule b vb))))
va (fun zenon_H6=>(zenon_imply _ _ (fun zenon_H5=>(zenon_H5 zenon_H4)) (
fun zenon_H2=>(zenon_H3 zenon_H2)) zenon_H6)) zenon_H7))
_p_V_consistency_rule_symmetric)) zenon_G)))).
Qed.

                Theorem __C_1_2_2_1_1_1_LEMMA :
                  Is_true ((_p_V_consistency_rule vb va)) ->
                    Is_true ((_p_V_consistency_rule va vb)).
                assert (__force_use_H221 := H221).
                assert (__force_use_H22 := H22).
                assert (__force_use_H2 := H2).
                apply for_zenon___C_1_2_2_1_1_1_LEMMA;
                auto.
                Qed.
                End __C_1_2_2_1_1_1.
(* File "vote.fcl", line 585, characters 20-46 *)
Theorem for_zenon___C_1_2_2_1_1_LEMMA:(~(Is_true (_p_V_consistency_rule
vb va))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G (fun zenon_H4=>(zenon_imply _ _ (fun
zenon_H5=>(zenon_H5 zenon_H4)) (fun zenon_H3=>(H2 zenon_H3))
__C_1_2_2_1_1_1_LEMMA)))))).
Qed.

              Theorem __C_1_2_2_1_1_LEMMA :
                ~Is_true (((_p_V_consistency_rule vb va))).
              assert (__force_use_H221 := H221).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_1_1_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_1_1.
            Section __C_1_2_2_1_2.
(* File "vote.fcl", line 587, characters 11-61 *)
Theorem for_zenon___C_1_2_2_1_2_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vb)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((~(Is_true (_p_V_consistency_rule v1 v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_range_match)))))))) va (fun zenon_H11=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule va v2)))
/\((~(Is_true (_p_V_consistency_rule va v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_range_match))))))) vb (fun zenon_H10=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule va vb)))/\((~(Is_true (
_p_V_consistency_rule va v3)))/\(Is_true (_p_V_consistency_rule vb v3)))
)->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) vb))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_1 _p_E_range_match)))))) vc (fun zenon_Hf=>(
zenon_imply _ _ (fun zenon_He=>(zenon_notand _ _ (fun zenon_Hd=>(
zenon_Hd (fun zenon_Hc=>(H2 zenon_Hc)))) (fun zenon_Hb=>(zenon_notand _
_ (fun zenon_Ha=>(zenon_Ha (fun zenon_H9=>(H22 zenon_H9)))) (fun
zenon_H8=>(zenon_H8 H221)) zenon_Hb)) zenon_He)) (fun zenon_H7=>(
zenon_and _ _ (fun zenon_H5 zenon_H6=>(zenon_G zenon_H5)) zenon_H7))
zenon_Hf)) zenon_H10)) zenon_H11)) abst_vote_match_c1)))).
Qed.

              Theorem __C_1_2_2_1_2_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter va vb vc)) vb))).
              assert (__force_use_H221 := H221).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_1_2_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_1_2.
            Section __C_1_2_2_1_3.
(* File "vote.fcl", line 589, characters 11-67 *)
Theorem for_zenon___C_1_2_2_1_3_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter vb va vc)) vc)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((Is_true (_p_V_consistency_rule v1 v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_range_match)))))))) vb (fun zenon_H11=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule vb v2)))
/\((Is_true (_p_V_consistency_rule vb v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vb v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_range_match))))))) va (fun zenon_H10=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule vb va)))/\((Is_true (
_p_V_consistency_rule vb v3))/\(~(Is_true (_p_V_consistency_rule va v3))
)))->((Is_true (basics._equal_ _ (abst_value (abst_voter vb va v3)) v3))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vb va v3)) (
_p_P_constr _p_C_capt_2 _p_E_range_match)))))) vc (fun zenon_Hf=>(
zenon_imply _ _ (fun zenon_He=>(zenon_notand _ _ (fun zenon_Hd=>(
zenon_Hd (fun zenon_Hc=>(__C_1_2_2_1_1_LEMMA zenon_Hc)))) (fun
zenon_Hb=>(zenon_notand _ _ (fun zenon_Ha=>(zenon_Ha H221)) (fun
zenon_H9=>(zenon_H9 (fun zenon_H8=>(H22 zenon_H8)))) zenon_Hb))
zenon_He)) (fun zenon_H7=>(zenon_and _ _ (fun zenon_H5 zenon_H6=>(
zenon_G zenon_H5)) zenon_H7)) zenon_Hf)) zenon_H10)) zenon_H11))
abst_vote_match_c2)))).
Qed.

              Theorem __C_1_2_2_1_3_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter vb va vc)) vc))).
              assert (__force_use_H221 := H221).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_1_3_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_1_3.
            Section __C_1_2_2_1_4.
              Section __C_1_2_2_1_4_1.
(* File "vote.fcl", line 592, characters 12-52 *)
Theorem for_zenon___C_1_2_2_1_4_1_LEMMA:((Is_true (
_p_V_consistency_rule vc va))->(Is_true (_p_V_consistency_rule va vc))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notimply _ _ (fun zenon_H4 zenon_H3=>(
zenon_all _p_V_T (fun a:_p_V_T=>(forall b:_p_V_T,((Is_true (
_p_V_consistency_rule a b))->(Is_true (_p_V_consistency_rule b a)))))
vc (fun zenon_H7=>(zenon_all _p_V_T (fun b:_p_V_T=>((Is_true (
_p_V_consistency_rule vc b))->(Is_true (_p_V_consistency_rule b vc))))
va (fun zenon_H6=>(zenon_imply _ _ (fun zenon_H5=>(zenon_H5 zenon_H4)) (
fun zenon_H2=>(zenon_H3 zenon_H2)) zenon_H6)) zenon_H7))
_p_V_consistency_rule_symmetric)) zenon_G)))).
Qed.

                Theorem __C_1_2_2_1_4_1_LEMMA :
                  Is_true ((_p_V_consistency_rule vc va)) ->
                    Is_true ((_p_V_consistency_rule va vc)).
                assert (__force_use_H221 := H221).
                assert (__force_use_H22 := H22).
                assert (__force_use_H2 := H2).
                apply for_zenon___C_1_2_2_1_4_1_LEMMA;
                auto.
                Qed.
                End __C_1_2_2_1_4_1.
(* File "vote.fcl", line 593, characters 20-47 *)
Theorem for_zenon___C_1_2_2_1_4_LEMMA:(~(Is_true (_p_V_consistency_rule
vc va))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G (fun zenon_H4=>(zenon_imply _ _ (fun
zenon_H5=>(zenon_H5 zenon_H4)) (fun zenon_H3=>(H22 zenon_H3))
__C_1_2_2_1_4_1_LEMMA)))))).
Qed.

              Theorem __C_1_2_2_1_4_LEMMA :
                ~Is_true (((_p_V_consistency_rule vc va))).
              assert (__force_use_H221 := H221).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_1_4_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_1_4.
            Section __C_1_2_2_1_5.
(* File "vote.fcl", line 595, character 11, line 596, character 67 *)
Theorem for_zenon___C_1_2_2_1_5_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter vc va vb)) vb)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((Is_true (_p_V_consistency_rule v1 v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_range_match)))))))) vc (fun zenon_H16=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule vc v2)))
/\((Is_true (_p_V_consistency_rule vc v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vc v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_range_match))))))) va (fun zenon_H15=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule vc va)))/\((Is_true (
_p_V_consistency_rule vc v3))/\(~(Is_true (_p_V_consistency_rule va v3))
)))->((Is_true (basics._equal_ _ (abst_value (abst_voter vc va v3)) v3))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vc va v3)) (
_p_P_constr _p_C_capt_2 _p_E_range_match)))))) vb (fun zenon_H14=>(
zenon_imply _ _ (fun zenon_H13=>(zenon_notand _ _ (fun zenon_H12=>(
zenon_H12 (fun zenon_H11=>(__C_1_2_2_1_4_LEMMA zenon_H11)))) (fun
zenon_H10=>(zenon_notand _ _ (fun zenon_Hc=>(zenon_all _p_V_T (fun v1
:_p_V_T=>(forall v2:_p_V_T,((Is_true (_p_V_consistency_rule v1 v2))->(
Is_true (_p_V_consistency_rule v2 v1))))) vb (fun zenon_Hf=>(zenon_all
_p_V_T (fun v2:_p_V_T=>((Is_true (_p_V_consistency_rule vb v2))->(
Is_true (_p_V_consistency_rule v2 vb)))) vc (fun zenon_He=>(zenon_imply
_ _ (fun zenon_Hd=>(zenon_Hd H221)) (fun zenon_Hb=>(zenon_Hc zenon_Hb))
zenon_He)) zenon_Hf)) abst_consistency_rule_is_symmetric)) (fun
zenon_Ha=>(zenon_Ha (fun zenon_H9=>(H2 zenon_H9)))) zenon_H10))
zenon_H13)) (fun zenon_H8=>(zenon_and _ _ (fun zenon_H6 zenon_H7=>(
zenon_G zenon_H6)) zenon_H8)) zenon_H14)) zenon_H15)) zenon_H16))
abst_vote_match_c2)))).
Qed.

              Theorem __C_1_2_2_1_5_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_value (abst_voter vc va vb)) vb))).
              assert (__force_use_H221 := H221).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_1_5_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_1_5.
            Section __C_1_2_2_1_6.
(* File "vote.fcl", line 600, characters 11-61 *)
Theorem for_zenon___C_1_2_2_1_6_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter va vb vc)) (_p_P_constr _p_C_capt_1
_p_E_range_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((~(Is_true (_p_V_consistency_rule v1 v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_range_match)))))))) va (fun zenon_H11=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule va v2)))
/\((~(Is_true (_p_V_consistency_rule va v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_range_match))))))) vb (fun zenon_H10=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule va vb)))/\((~(Is_true (
_p_V_consistency_rule va v3)))/\(Is_true (_p_V_consistency_rule vb v3)))
)->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) vb))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_1 _p_E_range_match)))))) vc (fun zenon_Hf=>(
zenon_imply _ _ (fun zenon_He=>(zenon_notand _ _ (fun zenon_Hd=>(
zenon_Hd (fun zenon_Hc=>(H2 zenon_Hc)))) (fun zenon_Hb=>(zenon_notand _
_ (fun zenon_Ha=>(zenon_Ha (fun zenon_H9=>(H22 zenon_H9)))) (fun
zenon_H8=>(zenon_H8 H221)) zenon_Hb)) zenon_He)) (fun zenon_H7=>(
zenon_and _ _ (fun zenon_H6 zenon_H5=>(zenon_G zenon_H5)) zenon_H7))
zenon_Hf)) zenon_H10)) zenon_H11)) abst_vote_match_c1)))).
Qed.

              Theorem __C_1_2_2_1_6_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter va vb vc))
                            (_p_P_constr _p_C_capt_1 _p_E_range_match)))).
              assert (__force_use_H221 := H221).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_1_6_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_1_6.
            Section __C_1_2_2_1_7.
(* File "vote.fcl", line 602, characters 11-79 *)
Theorem for_zenon___C_1_2_2_1_7_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter va vb vc)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter va vb vc)) (_p_P_constr
_p_C_capt_1 _p_E_range_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_range_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter va vb vc)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_1 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 n2)) n2))) _p_E_range_match (fun zenon_H6=>(zenon_subst _ (
fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 _p_E_range_match)) _p_E_range_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter va vb vc))) _p_E_range_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_range_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter va
vb vc))) _p_E_range_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_1
_p_E_range_match)) (_p_P_prj_b (abst_diag (abst_voter va vb vc))) (fun
zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter va vb vc)))))) (_p_P_constr
_p_C_capt_1 _p_E_range_match) (abst_diag (abst_voter va vb vc)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter va vb vc)) (_p_P_constr
_p_C_capt_1 _p_E_range_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter va vb vc))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter va vb vc))) _p_E_range_match))) zenon_H7)) zenon_H5 zenon_H6)
) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(zenon_G
zenon_H4)) zenon_Hc)) _p_P_range_match_is_valid)) __C_1_2_2_1_6_LEMMA)))
).
Qed.

              Theorem __C_1_2_2_1_7_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter va vb vc))))).
              assert (__force_use_H221 := H221).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_1_7_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_1_7.
            Section __C_1_2_2_1_8.
(* File "vote.fcl", line 606, characters 10-66 *)
Theorem for_zenon___C_1_2_2_1_8_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb va vc)) (_p_P_constr _p_C_capt_2
_p_E_range_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((Is_true (_p_V_consistency_rule v1 v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_range_match)))))))) vb (fun zenon_H11=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule vb v2)))
/\((Is_true (_p_V_consistency_rule vb v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vb v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_range_match))))))) va (fun zenon_H10=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule vb va)))/\((Is_true (
_p_V_consistency_rule vb v3))/\(~(Is_true (_p_V_consistency_rule va v3))
)))->((Is_true (basics._equal_ _ (abst_value (abst_voter vb va v3)) v3))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vb va v3)) (
_p_P_constr _p_C_capt_2 _p_E_range_match)))))) vc (fun zenon_Hf=>(
zenon_imply _ _ (fun zenon_He=>(zenon_notand _ _ (fun zenon_Hd=>(
zenon_Hd (fun zenon_Hc=>(__C_1_2_2_1_1_LEMMA zenon_Hc)))) (fun
zenon_Hb=>(zenon_notand _ _ (fun zenon_Ha=>(zenon_Ha H221)) (fun
zenon_H9=>(zenon_H9 (fun zenon_H8=>(H22 zenon_H8)))) zenon_Hb))
zenon_He)) (fun zenon_H7=>(zenon_and _ _ (fun zenon_H6 zenon_H5=>(
zenon_G zenon_H5)) zenon_H7)) zenon_Hf)) zenon_H10)) zenon_H11))
abst_vote_match_c2)))).
Qed.

              Theorem __C_1_2_2_1_8_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter vb va vc))
                            (_p_P_constr _p_C_capt_2 _p_E_range_match)))).
              assert (__force_use_H221 := H221).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_1_8_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_1_8.
            Section __C_1_2_2_1_9.
(* File "vote.fcl", line 608, characters 10-78 *)
Theorem for_zenon___C_1_2_2_1_9_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter vb va vc)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter vb va vc)) (_p_P_constr
_p_C_capt_2 _p_E_range_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_range_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter vb va vc)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_2 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_2 n2)) n2))) _p_E_range_match (fun zenon_H6=>(zenon_subst _ (
fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_2 _p_E_range_match)) _p_E_range_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter vb va vc))) _p_E_range_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_range_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vb
va vc))) _p_E_range_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_2
_p_E_range_match)) (_p_P_prj_b (abst_diag (abst_voter vb va vc))) (fun
zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter vb va vc)))))) (_p_P_constr
_p_C_capt_2 _p_E_range_match) (abst_diag (abst_voter vb va vc)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter vb va vc)) (_p_P_constr
_p_C_capt_2 _p_E_range_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter vb va vc))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter vb va vc))) _p_E_range_match))) zenon_H7)) zenon_H5 zenon_H6)
) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(zenon_G
zenon_H4)) zenon_Hc)) _p_P_range_match_is_valid)) __C_1_2_2_1_8_LEMMA)))
).
Qed.

              Theorem __C_1_2_2_1_9_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter vb va vc))))).
              assert (__force_use_H221 := H221).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_1_9_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_1_9.
            Section __C_1_2_2_1_10.
(* File "vote.fcl", line 612, character 10, line 613, character 63 *)
Theorem for_zenon___C_1_2_2_1_10_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc va vb)) (_p_P_constr _p_C_capt_2
_p_E_range_match))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((Is_true (_p_V_consistency_rule v1 v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_range_match)))))))) vc (fun zenon_H16=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule vc v2)))
/\((Is_true (_p_V_consistency_rule vc v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter vc v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_range_match))))))) va (fun zenon_H15=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule vc va)))/\((Is_true (
_p_V_consistency_rule vc v3))/\(~(Is_true (_p_V_consistency_rule va v3))
)))->((Is_true (basics._equal_ _ (abst_value (abst_voter vc va v3)) v3))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter vc va v3)) (
_p_P_constr _p_C_capt_2 _p_E_range_match)))))) vb (fun zenon_H14=>(
zenon_imply _ _ (fun zenon_H13=>(zenon_notand _ _ (fun zenon_H12=>(
zenon_H12 (fun zenon_H11=>(__C_1_2_2_1_4_LEMMA zenon_H11)))) (fun
zenon_H10=>(zenon_notand _ _ (fun zenon_Hc=>(zenon_all _p_V_T (fun v1
:_p_V_T=>(forall v2:_p_V_T,((Is_true (_p_V_consistency_rule v1 v2))->(
Is_true (_p_V_consistency_rule v2 v1))))) vb (fun zenon_Hf=>(zenon_all
_p_V_T (fun v2:_p_V_T=>((Is_true (_p_V_consistency_rule vb v2))->(
Is_true (_p_V_consistency_rule v2 vb)))) vc (fun zenon_He=>(zenon_imply
_ _ (fun zenon_Hd=>(zenon_Hd H221)) (fun zenon_Hb=>(zenon_Hc zenon_Hb))
zenon_He)) zenon_Hf)) abst_consistency_rule_is_symmetric)) (fun
zenon_Ha=>(zenon_Ha (fun zenon_H9=>(H2 zenon_H9)))) zenon_H10))
zenon_H13)) (fun zenon_H8=>(zenon_and _ _ (fun zenon_H7 zenon_H6=>(
zenon_G zenon_H6)) zenon_H8)) zenon_H14)) zenon_H15)) zenon_H16))
abst_vote_match_c2)))).
Qed.

              Theorem __C_1_2_2_1_10_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter vc va vb))
                            (_p_P_constr _p_C_capt_2 _p_E_range_match)))).
              assert (__force_use_H221 := H221).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_1_10_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_1_10.
            Section __C_1_2_2_1_11.
(* File "vote.fcl", line 615, characters 10-79 *)
Theorem for_zenon___C_1_2_2_1_11_LEMMA:(Is_true (_p_P_valid (abst_diag (
abst_voter vc va vb)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter vc va vb)) (_p_P_constr
_p_C_capt_2 _p_E_range_match) (fun zenon_H9=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_range_match))->(
Is_true (_p_P_valid x)))) (abst_diag (abst_voter vc va vb)) (fun
zenon_Hc=>(zenon_imply _ _ (fun zenon_H5=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_2 (fun zenon_Hb=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_2 n2)) n2))) _p_E_range_match (fun zenon_H6=>(zenon_subst _ (
fun zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_2 _p_E_range_match)) _p_E_range_match) (_p_E_equal (
_p_P_prj_b (abst_diag (abst_voter vc va vb))) _p_E_range_match) (fun
zenon_H7=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_range_match) = (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vc
va vb))) _p_E_range_match)))) (_p_P_prj_b (_p_P_constr _p_C_capt_2
_p_E_range_match)) (_p_P_prj_b (abst_diag (abst_voter vc va vb))) (fun
zenon_H8=>(zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter vc va vb)))))) (_p_P_constr
_p_C_capt_2 _p_E_range_match) (abst_diag (abst_voter vc va vb)) (fun
zenon_Ha=>(zenon_eqsym _ (abst_diag (abst_voter vc va vb)) (_p_P_constr
_p_C_capt_2 _p_E_range_match) zenon_H9 zenon_Ha)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter vc va vb))))) zenon_H8)) (
zenon_notnot _ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (
abst_voter vc va vb))) _p_E_range_match))) zenon_H7)) zenon_H5 zenon_H6)
) zenon_Hb)) _p_P_prj_b_is_snd_of_pair)) (fun zenon_H4=>(zenon_G
zenon_H4)) zenon_Hc)) _p_P_range_match_is_valid)) __C_1_2_2_1_10_LEMMA))
)).
Qed.

              Theorem __C_1_2_2_1_11_LEMMA :
                Is_true (((_p_P_valid (abst_diag (abst_voter vc va vb))))).
              assert (__force_use_H221 := H221).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_1_11_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_1_11.
(* File "vote.fcl", line 618, character 18, line 620, character 38 *)
Theorem for_zenon___C_1_2_2_1_LEMMA:((abst_compatible (abst_voter va vb
vc) (abst_voter vb va vc))/\(abst_compatible (abst_voter va vb vc) (
abst_voter vc va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notand _ _ (fun zenon_H21=>(let zenon_H20
:=zenon_H21 in (zenon_notor _ _ (fun zenon_H1e zenon_H1f=>(zenon_notand
_ _ (fun zenon_H12=>(zenon_H12 __C_1_2_2_1_7_LEMMA)) (fun zenon_H1d=>(
zenon_notand _ _ (fun zenon_H1c=>(zenon_H1c __C_1_2_2_1_9_LEMMA)) (fun
zenon_H17=>(coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (
abst_value (abst_voter va vb vc)) vb (fun zenon_Hd=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (abst_value (
abst_voter vb va vc)) vc (fun zenon_H19=>(zenon_subst _ (fun zenon_Vi=>(
Is_true zenon_Vi)) (_p_V_consistency_rule vb vc) (_p_V_consistency_rule
(abst_value (abst_voter va vb vc)) (abst_value (abst_voter vb va vc))) (
fun zenon_H18=>(zenon_subst _ (fun zenon_Vk=>(~((_p_V_consistency_rule
zenon_Vk vc) = (_p_V_consistency_rule (abst_value (abst_voter va vb vc))
 (abst_value (abst_voter vb va vc)))))) vb (abst_value (abst_voter va
vb vc)) (fun zenon_H1b=>(zenon_eqsym _ (abst_value (abst_voter va vb vc)
) vb zenon_Hd zenon_H1b)) (zenon_subst _ (fun zenon_Vj=>(~((
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) zenon_Vj) = (
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vb va vc)))))) vc (abst_value (abst_voter vb va vc)) (fun
zenon_H1a=>(zenon_eqsym _ (abst_value (abst_voter vb va vc)) vc
zenon_H19 zenon_H1a)) (zenon_notnot _ (refl_equal (
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vb va vc)))))) zenon_H18)) zenon_H17 H221))
__C_1_2_2_1_3_LEMMA)) __C_1_2_2_1_2_LEMMA)) zenon_H1d)) zenon_H1e))
zenon_H20))) (fun zenon_H16=>(let zenon_H15:=zenon_H16 in (zenon_notor
_ _ (fun zenon_H13 zenon_H14=>(zenon_notand _ _ (fun zenon_H12=>(
zenon_H12 __C_1_2_2_1_7_LEMMA)) (fun zenon_H11=>(zenon_notand _ _ (fun
zenon_H10=>(zenon_H10 __C_1_2_2_1_11_LEMMA)) (fun zenon_H9=>(zenon_all
_p_V_T (fun a:_p_V_T=>(Is_true (_p_V_consistency_rule a a))) (
abst_value (abst_voter va vb vc)) (fun zenon_Ha=>(zenon_subst _ (fun
zenon_Vf=>(Is_true zenon_Vf)) (_p_V_consistency_rule (abst_value (
abst_voter va vb vc)) (abst_value (abst_voter va vb vc))) (
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vc va vb))) (fun zenon_Hb=>(zenon_subst _ (fun zenon_Vg=>(~((
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) zenon_Vg) = (
_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vc va vb)))))) (abst_value (abst_voter va vb vc)) (
abst_value (abst_voter vc va vb)) (fun zenon_Hc=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (abst_value (
abst_voter va vb vc)) vb (fun zenon_Hd=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ (abst_value (
abst_voter vc va vb)) vb (fun zenon_He=>(zenon_subst _ (fun zenon_Vh=>((
abst_value (abst_voter va vb vc)) = zenon_Vh)) vb (abst_value (
abst_voter vc va vb)) (fun zenon_Hf=>(zenon_eqsym _ (abst_value (
abst_voter vc va vb)) vb zenon_He zenon_Hf)) zenon_Hc zenon_Hd))
__C_1_2_2_1_5_LEMMA)) __C_1_2_2_1_2_LEMMA)) (zenon_notnot _ (refl_equal
(_p_V_consistency_rule (abst_value (abst_voter va vb vc)) (abst_value (
abst_voter vc va vb))))) zenon_Hb)) zenon_H9 zenon_Ha))
_p_V_consistency_rule_reflexive)) zenon_H11)) zenon_H13)) zenon_H15)))
zenon_G)))).
Qed.

            Theorem __C_1_2_2_1_LEMMA :
              ((abst_compatible (abst_voter va vb vc) (abst_voter vb va vc)) /\
                 (abst_compatible (abst_voter va vb vc)
                   (abst_voter vc va vb))).
            assert (__force_use_H221 := H221).
            assert (__force_use_H22 := H22).
            assert (__force_use_H2 := H2).
            apply for_zenon___C_1_2_2_1_LEMMA;
            auto.
            Qed.
            End __C_1_2_2_1.
          Section __C_1_2_2_2.
            Variable H222 : ~Is_true (((_p_V_consistency_rule vb vc))).
            Section __C_1_2_2_2_1.
              Section __C_1_2_2_2_1_1.
(* File "vote.fcl", line 631, characters 12-52 *)
Theorem for_zenon___C_1_2_2_2_1_1_LEMMA:((Is_true (
_p_V_consistency_rule vb va))->(Is_true (_p_V_consistency_rule va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notimply _ _ (fun zenon_H4 zenon_H3=>(
zenon_all _p_V_T (fun a:_p_V_T=>(forall b:_p_V_T,((Is_true (
_p_V_consistency_rule a b))->(Is_true (_p_V_consistency_rule b a)))))
vb (fun zenon_H7=>(zenon_all _p_V_T (fun b:_p_V_T=>((Is_true (
_p_V_consistency_rule vb b))->(Is_true (_p_V_consistency_rule b vb))))
va (fun zenon_H6=>(zenon_imply _ _ (fun zenon_H5=>(zenon_H5 zenon_H4)) (
fun zenon_H2=>(zenon_H3 zenon_H2)) zenon_H6)) zenon_H7))
_p_V_consistency_rule_symmetric)) zenon_G)))).
Qed.

                Theorem __C_1_2_2_2_1_1_LEMMA :
                  Is_true ((_p_V_consistency_rule vb va)) ->
                    Is_true ((_p_V_consistency_rule va vb)).
                assert (__force_use_H222 := H222).
                assert (__force_use_H22 := H22).
                assert (__force_use_H2 := H2).
                apply for_zenon___C_1_2_2_2_1_1_LEMMA;
                auto.
                Qed.
                End __C_1_2_2_2_1_1.
(* File "vote.fcl", line 632, characters 20-46 *)
Theorem for_zenon___C_1_2_2_2_1_LEMMA:(~(Is_true (_p_V_consistency_rule
vb va))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G (fun zenon_H4=>(zenon_imply _ _ (fun
zenon_H5=>(zenon_H5 zenon_H4)) (fun zenon_H3=>(H2 zenon_H3))
__C_1_2_2_2_1_1_LEMMA)))))).
Qed.

              Theorem __C_1_2_2_2_1_LEMMA :
                ~Is_true (((_p_V_consistency_rule vb va))).
              assert (__force_use_H222 := H222).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_2_1_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_2_1.
            Section __C_1_2_2_2_2.
              Section __C_1_2_2_2_2_1.
(* File "vote.fcl", line 635, characters 12-52 *)
Theorem for_zenon___C_1_2_2_2_2_1_LEMMA:((Is_true (
_p_V_consistency_rule vc va))->(Is_true (_p_V_consistency_rule va vc))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notimply _ _ (fun zenon_H4 zenon_H3=>(
zenon_all _p_V_T (fun a:_p_V_T=>(forall b:_p_V_T,((Is_true (
_p_V_consistency_rule a b))->(Is_true (_p_V_consistency_rule b a)))))
vc (fun zenon_H7=>(zenon_all _p_V_T (fun b:_p_V_T=>((Is_true (
_p_V_consistency_rule vc b))->(Is_true (_p_V_consistency_rule b vc))))
va (fun zenon_H6=>(zenon_imply _ _ (fun zenon_H5=>(zenon_H5 zenon_H4)) (
fun zenon_H2=>(zenon_H3 zenon_H2)) zenon_H6)) zenon_H7))
_p_V_consistency_rule_symmetric)) zenon_G)))).
Qed.

                Theorem __C_1_2_2_2_2_1_LEMMA :
                  Is_true ((_p_V_consistency_rule vc va)) ->
                    Is_true ((_p_V_consistency_rule va vc)).
                assert (__force_use_H222 := H222).
                assert (__force_use_H22 := H22).
                assert (__force_use_H2 := H2).
                apply for_zenon___C_1_2_2_2_2_1_LEMMA;
                auto.
                Qed.
                End __C_1_2_2_2_2_1.
(* File "vote.fcl", line 636, characters 20-47 *)
Theorem for_zenon___C_1_2_2_2_2_LEMMA:(~(Is_true (_p_V_consistency_rule
vc va))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G (fun zenon_H4=>(zenon_imply _ _ (fun
zenon_H5=>(zenon_H5 zenon_H4)) (fun zenon_H3=>(H22 zenon_H3))
__C_1_2_2_2_2_1_LEMMA)))))).
Qed.

              Theorem __C_1_2_2_2_2_LEMMA :
                ~Is_true (((_p_V_consistency_rule vc va))).
              assert (__force_use_H222 := H222).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_2_2_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_2_2.
            Section __C_1_2_2_2_3.
              Section __C_1_2_2_2_3_1.
(* File "vote.fcl", line 639, characters 12-52 *)
Theorem for_zenon___C_1_2_2_2_3_1_LEMMA:((Is_true (
_p_V_consistency_rule vc vb))->(Is_true (_p_V_consistency_rule vb vc))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notimply _ _ (fun zenon_H4 zenon_H3=>(
zenon_all _p_V_T (fun a:_p_V_T=>(forall b:_p_V_T,((Is_true (
_p_V_consistency_rule a b))->(Is_true (_p_V_consistency_rule b a)))))
vc (fun zenon_H7=>(zenon_all _p_V_T (fun b:_p_V_T=>((Is_true (
_p_V_consistency_rule vc b))->(Is_true (_p_V_consistency_rule b vc))))
vb (fun zenon_H6=>(zenon_imply _ _ (fun zenon_H5=>(zenon_H5 zenon_H4)) (
fun zenon_H2=>(zenon_H3 zenon_H2)) zenon_H6)) zenon_H7))
_p_V_consistency_rule_symmetric)) zenon_G)))).
Qed.

                Theorem __C_1_2_2_2_3_1_LEMMA :
                  Is_true ((_p_V_consistency_rule vc vb)) ->
                    Is_true ((_p_V_consistency_rule vb vc)).
                assert (__force_use_H222 := H222).
                assert (__force_use_H22 := H22).
                assert (__force_use_H2 := H2).
                apply for_zenon___C_1_2_2_2_3_1_LEMMA;
                auto.
                Qed.
                End __C_1_2_2_2_3_1.
(* File "vote.fcl", line 640, characters 20-48 *)
Theorem for_zenon___C_1_2_2_2_3_LEMMA:(~(Is_true (_p_V_consistency_rule
vc vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G (fun zenon_H4=>(zenon_imply _ _ (fun
zenon_H5=>(zenon_H5 zenon_H4)) (fun zenon_H3=>(H222 zenon_H3))
__C_1_2_2_2_3_1_LEMMA)))))).
Qed.

              Theorem __C_1_2_2_2_3_LEMMA :
                ~Is_true (((_p_V_consistency_rule vc vb))).
              assert (__force_use_H222 := H222).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_2_3_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_2_3.
            Section __C_1_2_2_2_4.
(* File "vote.fcl", line 643, characters 10-60 *)
Theorem for_zenon___C_1_2_2_2_4_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter va vb vc)) (_p_P_constr _p_C_capt_1 _p_E_no_match)
)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((~(Is_true (_p_V_consistency_rule v1 v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->(Is_true (basics._equal_ _ (abst_diag
(abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1 _p_E_no_match))))))) va
(fun zenon_H10=>(zenon_all _p_V_T (fun v2:_p_V_T=>(forall v3:_p_V_T,(((~
(Is_true (_p_V_consistency_rule va v2)))/\((~(Is_true (
_p_V_consistency_rule va v3)))/\(~(Is_true (_p_V_consistency_rule v2 v3)
))))->(Is_true (basics._equal_ _ (abst_diag (abst_voter va v2 v3)) (
_p_P_constr _p_C_capt_1 _p_E_no_match)))))) vb (fun zenon_Hf=>(
zenon_all _p_V_T (fun v3:_p_V_T=>(((~(Is_true (_p_V_consistency_rule va
vb)))/\((~(Is_true (_p_V_consistency_rule va v3)))/\(~(Is_true (
_p_V_consistency_rule vb v3)))))->(Is_true (basics._equal_ _ (abst_diag
(abst_voter va vb v3)) (_p_P_constr _p_C_capt_1 _p_E_no_match))))) vc (
fun zenon_He=>(zenon_imply _ _ (fun zenon_Hd=>(zenon_notand _ _ (fun
zenon_Hc=>(zenon_Hc (fun zenon_Hb=>(H2 zenon_Hb)))) (fun zenon_Ha=>(
zenon_notand _ _ (fun zenon_H9=>(zenon_H9 (fun zenon_H8=>(H22 zenon_H8))
)) (fun zenon_H7=>(zenon_H7 (fun zenon_H6=>(H222 zenon_H6)))) zenon_Ha))
 zenon_Hd)) (fun zenon_H5=>(zenon_G zenon_H5)) zenon_He)) zenon_Hf))
zenon_H10)) abst_vote_no_match)))).
Qed.

              Theorem __C_1_2_2_2_4_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter va vb vc))
                            (_p_P_constr _p_C_capt_1 _p_E_no_match)))).
              assert (__force_use_H222 := H222).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_2_4_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_2_4.
            Section __C_1_2_2_2_5.
(* File "vote.fcl", line 645, characters 10-54 *)
Theorem for_zenon___C_1_2_2_2_5_LEMMA:(Is_true (_p_E_equal (_p_P_prj_b (
abst_diag (abst_voter va vb vc))) _p_E_no_match)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter va vb vc)) (_p_P_constr
_p_C_capt_1 _p_E_no_match) (fun zenon_H6=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_1 (fun zenon_H8=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 n2)) n2))) _p_E_no_match (fun zenon_H3=>(zenon_subst _ (fun
zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 _p_E_no_match)) _p_E_no_match) (_p_E_equal (_p_P_prj_b (
abst_diag (abst_voter va vb vc))) _p_E_no_match) (fun zenon_H4=>(
zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg _p_E_no_match) = (
_p_E_equal (_p_P_prj_b (abst_diag (abst_voter va vb vc))) _p_E_no_match)
))) (_p_P_prj_b (_p_P_constr _p_C_capt_1 _p_E_no_match)) (_p_P_prj_b (
abst_diag (abst_voter va vb vc))) (fun zenon_H5=>(zenon_subst _ (fun
zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (_p_P_prj_b (abst_diag (abst_voter
va vb vc)))))) (_p_P_constr _p_C_capt_1 _p_E_no_match) (abst_diag (
abst_voter va vb vc)) (fun zenon_H7=>(zenon_eqsym _ (abst_diag (
abst_voter va vb vc)) (_p_P_constr _p_C_capt_1 _p_E_no_match) zenon_H6
zenon_H7)) (zenon_notnot _ (refl_equal (_p_P_prj_b (abst_diag (
abst_voter va vb vc))))) zenon_H5)) (zenon_notnot _ (refl_equal (
_p_E_equal (_p_P_prj_b (abst_diag (abst_voter va vb vc))) _p_E_no_match)
)) zenon_H4)) zenon_G zenon_H3)) zenon_H8)) _p_P_prj_b_is_snd_of_pair))
__C_1_2_2_2_4_LEMMA)))).
Qed.

              Theorem __C_1_2_2_2_5_LEMMA :
                Is_true (((_p_E_equal
                            (_p_P_prj_b (abst_diag (abst_voter va vb vc)))
                            _p_E_no_match))).
              assert (__force_use_H222 := H222).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_2_5_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_2_5.
            Section __C_1_2_2_2_51.
(* File "vote.fcl", line 647, characters 10-53 *)
Theorem for_zenon___C_1_2_2_2_51_LEMMA:(~(Is_true (_p_P_valid (
abst_diag (abst_voter va vb vc))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G (fun zenon_H3=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_no_match))->(~(
Is_true (_p_P_valid x))))) (abst_diag (abst_voter va vb vc)) (fun
zenon_H6=>(zenon_imply _ _ (fun zenon_H5=>(zenon_H5 __C_1_2_2_2_5_LEMMA)
) (fun zenon_H4=>(zenon_H4 zenon_H3)) zenon_H6))
_p_P_no_match_is_invalid)))))).
Qed.

              Theorem __C_1_2_2_2_51_LEMMA :
                ~Is_true (((_p_P_valid (abst_diag (abst_voter va vb vc))))).
              assert (__force_use_H222 := H222).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_2_51_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_2_51.
            Section __C_1_2_2_2_6.
(* File "vote.fcl", line 650, characters 10-66 *)
Theorem for_zenon___C_1_2_2_2_6_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter vb va vc)) (_p_P_constr _p_C_capt_1 _p_E_no_match)
)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((~(Is_true (_p_V_consistency_rule v1 v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->(Is_true (basics._equal_ _ (abst_diag
(abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1 _p_E_no_match))))))) vb
(fun zenon_H10=>(zenon_all _p_V_T (fun v2:_p_V_T=>(forall v3:_p_V_T,(((~
(Is_true (_p_V_consistency_rule vb v2)))/\((~(Is_true (
_p_V_consistency_rule vb v3)))/\(~(Is_true (_p_V_consistency_rule v2 v3)
))))->(Is_true (basics._equal_ _ (abst_diag (abst_voter vb v2 v3)) (
_p_P_constr _p_C_capt_1 _p_E_no_match)))))) va (fun zenon_Hf=>(
zenon_all _p_V_T (fun v3:_p_V_T=>(((~(Is_true (_p_V_consistency_rule vb
va)))/\((~(Is_true (_p_V_consistency_rule vb v3)))/\(~(Is_true (
_p_V_consistency_rule va v3)))))->(Is_true (basics._equal_ _ (abst_diag
(abst_voter vb va v3)) (_p_P_constr _p_C_capt_1 _p_E_no_match))))) vc (
fun zenon_He=>(zenon_imply _ _ (fun zenon_Hd=>(zenon_notand _ _ (fun
zenon_Hc=>(zenon_Hc (fun zenon_Hb=>(__C_1_2_2_2_1_LEMMA zenon_Hb)))) (
fun zenon_Ha=>(zenon_notand _ _ (fun zenon_H9=>(zenon_H9 (fun zenon_H8=>
(H222 zenon_H8)))) (fun zenon_H7=>(zenon_H7 (fun zenon_H6=>(H22
zenon_H6)))) zenon_Ha)) zenon_Hd)) (fun zenon_H5=>(zenon_G zenon_H5))
zenon_He)) zenon_Hf)) zenon_H10)) abst_vote_no_match)))).
Qed.

              Theorem __C_1_2_2_2_6_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter vb va vc))
                            (_p_P_constr _p_C_capt_1 _p_E_no_match)))).
              assert (__force_use_H222 := H222).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_2_6_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_2_6.
            Section __C_1_2_2_2_7.
(* File "vote.fcl", line 652, characters 10-54 *)
Theorem for_zenon___C_1_2_2_2_7_LEMMA:(Is_true (_p_E_equal (_p_P_prj_b (
abst_diag (abst_voter vb va vc))) _p_E_no_match)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter vb va vc)) (_p_P_constr
_p_C_capt_1 _p_E_no_match) (fun zenon_H6=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_1 (fun zenon_H8=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 n2)) n2))) _p_E_no_match (fun zenon_H3=>(zenon_subst _ (fun
zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 _p_E_no_match)) _p_E_no_match) (_p_E_equal (_p_P_prj_b (
abst_diag (abst_voter vb va vc))) _p_E_no_match) (fun zenon_H4=>(
zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg _p_E_no_match) = (
_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vb va vc))) _p_E_no_match)
))) (_p_P_prj_b (_p_P_constr _p_C_capt_1 _p_E_no_match)) (_p_P_prj_b (
abst_diag (abst_voter vb va vc))) (fun zenon_H5=>(zenon_subst _ (fun
zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (_p_P_prj_b (abst_diag (abst_voter
vb va vc)))))) (_p_P_constr _p_C_capt_1 _p_E_no_match) (abst_diag (
abst_voter vb va vc)) (fun zenon_H7=>(zenon_eqsym _ (abst_diag (
abst_voter vb va vc)) (_p_P_constr _p_C_capt_1 _p_E_no_match) zenon_H6
zenon_H7)) (zenon_notnot _ (refl_equal (_p_P_prj_b (abst_diag (
abst_voter vb va vc))))) zenon_H5)) (zenon_notnot _ (refl_equal (
_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vb va vc))) _p_E_no_match)
)) zenon_H4)) zenon_G zenon_H3)) zenon_H8)) _p_P_prj_b_is_snd_of_pair))
__C_1_2_2_2_6_LEMMA)))).
Qed.

              Theorem __C_1_2_2_2_7_LEMMA :
                Is_true (((_p_E_equal
                            (_p_P_prj_b (abst_diag (abst_voter vb va vc)))
                            _p_E_no_match))).
              assert (__force_use_H222 := H222).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_2_7_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_2_7.
            Section __C_1_2_2_2_71.
(* File "vote.fcl", line 654, characters 10-53 *)
Theorem for_zenon___C_1_2_2_2_71_LEMMA:(~(Is_true (_p_P_valid (
abst_diag (abst_voter vb va vc))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G (fun zenon_H3=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_no_match))->(~(
Is_true (_p_P_valid x))))) (abst_diag (abst_voter vb va vc)) (fun
zenon_H6=>(zenon_imply _ _ (fun zenon_H5=>(zenon_H5 __C_1_2_2_2_7_LEMMA)
) (fun zenon_H4=>(zenon_H4 zenon_H3)) zenon_H6))
_p_P_no_match_is_invalid)))))).
Qed.

              Theorem __C_1_2_2_2_71_LEMMA :
                ~Is_true (((_p_P_valid (abst_diag (abst_voter vb va vc))))).
              assert (__force_use_H222 := H222).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_2_71_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_2_71.
            Section __C_1_2_2_2_8.
(* File "vote.fcl", line 657, characters 10-65 *)
Theorem for_zenon___C_1_2_2_2_8_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter vc va vb)) (_p_P_constr _p_C_capt_1 _p_E_no_match)
)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((~(Is_true (_p_V_consistency_rule v1 v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->(Is_true (basics._equal_ _ (abst_diag
(abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1 _p_E_no_match))))))) vc
(fun zenon_H10=>(zenon_all _p_V_T (fun v2:_p_V_T=>(forall v3:_p_V_T,(((~
(Is_true (_p_V_consistency_rule vc v2)))/\((~(Is_true (
_p_V_consistency_rule vc v3)))/\(~(Is_true (_p_V_consistency_rule v2 v3)
))))->(Is_true (basics._equal_ _ (abst_diag (abst_voter vc v2 v3)) (
_p_P_constr _p_C_capt_1 _p_E_no_match)))))) va (fun zenon_Hf=>(
zenon_all _p_V_T (fun v3:_p_V_T=>(((~(Is_true (_p_V_consistency_rule vc
va)))/\((~(Is_true (_p_V_consistency_rule vc v3)))/\(~(Is_true (
_p_V_consistency_rule va v3)))))->(Is_true (basics._equal_ _ (abst_diag
(abst_voter vc va v3)) (_p_P_constr _p_C_capt_1 _p_E_no_match))))) vb (
fun zenon_He=>(zenon_imply _ _ (fun zenon_Hd=>(zenon_notand _ _ (fun
zenon_Hc=>(zenon_Hc (fun zenon_Hb=>(__C_1_2_2_2_2_LEMMA zenon_Hb)))) (
fun zenon_Ha=>(zenon_notand _ _ (fun zenon_H9=>(zenon_H9 (fun zenon_H8=>
(__C_1_2_2_2_3_LEMMA zenon_H8)))) (fun zenon_H7=>(zenon_H7 (fun
zenon_H6=>(H2 zenon_H6)))) zenon_Ha)) zenon_Hd)) (fun zenon_H5=>(
zenon_G zenon_H5)) zenon_He)) zenon_Hf)) zenon_H10)) abst_vote_no_match)
))).
Qed.

              Theorem __C_1_2_2_2_8_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter vc va vb))
                            (_p_P_constr _p_C_capt_1 _p_E_no_match)))).
              assert (__force_use_H222 := H222).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_2_8_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_2_8.
            Section __C_1_2_2_2_9.
(* File "vote.fcl", line 659, characters 10-54 *)
Theorem for_zenon___C_1_2_2_2_9_LEMMA:(Is_true (_p_E_equal (_p_P_prj_b (
abst_diag (abst_voter vc va vb))) _p_E_no_match)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter vc va vb)) (_p_P_constr
_p_C_capt_1 _p_E_no_match) (fun zenon_H6=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_1 (fun zenon_H8=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 n2)) n2))) _p_E_no_match (fun zenon_H3=>(zenon_subst _ (fun
zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 _p_E_no_match)) _p_E_no_match) (_p_E_equal (_p_P_prj_b (
abst_diag (abst_voter vc va vb))) _p_E_no_match) (fun zenon_H4=>(
zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg _p_E_no_match) = (
_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vc va vb))) _p_E_no_match)
))) (_p_P_prj_b (_p_P_constr _p_C_capt_1 _p_E_no_match)) (_p_P_prj_b (
abst_diag (abst_voter vc va vb))) (fun zenon_H5=>(zenon_subst _ (fun
zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (_p_P_prj_b (abst_diag (abst_voter
vc va vb)))))) (_p_P_constr _p_C_capt_1 _p_E_no_match) (abst_diag (
abst_voter vc va vb)) (fun zenon_H7=>(zenon_eqsym _ (abst_diag (
abst_voter vc va vb)) (_p_P_constr _p_C_capt_1 _p_E_no_match) zenon_H6
zenon_H7)) (zenon_notnot _ (refl_equal (_p_P_prj_b (abst_diag (
abst_voter vc va vb))))) zenon_H5)) (zenon_notnot _ (refl_equal (
_p_E_equal (_p_P_prj_b (abst_diag (abst_voter vc va vb))) _p_E_no_match)
)) zenon_H4)) zenon_G zenon_H3)) zenon_H8)) _p_P_prj_b_is_snd_of_pair))
__C_1_2_2_2_8_LEMMA)))).
Qed.

              Theorem __C_1_2_2_2_9_LEMMA :
                Is_true (((_p_E_equal
                            (_p_P_prj_b (abst_diag (abst_voter vc va vb)))
                            _p_E_no_match))).
              assert (__force_use_H222 := H222).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_2_9_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_2_9.
            Section __C_1_2_2_2_91.
(* File "vote.fcl", line 661, characters 10-53 *)
Theorem for_zenon___C_1_2_2_2_91_LEMMA:(~(Is_true (_p_P_valid (
abst_diag (abst_voter vc va vb))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G (fun zenon_H3=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_no_match))->(~(
Is_true (_p_P_valid x))))) (abst_diag (abst_voter vc va vb)) (fun
zenon_H6=>(zenon_imply _ _ (fun zenon_H5=>(zenon_H5 __C_1_2_2_2_9_LEMMA)
) (fun zenon_H4=>(zenon_H4 zenon_H3)) zenon_H6))
_p_P_no_match_is_invalid)))))).
Qed.

              Theorem __C_1_2_2_2_91_LEMMA :
                ~Is_true (((_p_P_valid (abst_diag (abst_voter vc va vb))))).
              assert (__force_use_H222 := H222).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___C_1_2_2_2_91_LEMMA;
              auto.
              Qed.
              End __C_1_2_2_2_91.
(* File "vote.fcl", line 663, character 19, line 664, character 38 *)
Theorem for_zenon___C_1_2_2_2_LEMMA:((abst_compatible (abst_voter va vb
vc) (abst_voter vb va vc))/\(abst_compatible (abst_voter va vb vc) (
abst_voter vc va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notand _ _ (fun zenon_He=>(let zenon_Hd
:=zenon_He in (zenon_notor _ _ (fun zenon_Hc zenon_Hb=>(zenon_notand _
_ (fun zenon_H5=>(zenon_H5 __C_1_2_2_2_51_LEMMA)) (fun zenon_Ha=>(
zenon_Ha __C_1_2_2_2_71_LEMMA)) zenon_Hb)) zenon_Hd))) (fun zenon_H9=>(
let zenon_H8:=zenon_H9 in (zenon_notor _ _ (fun zenon_H7 zenon_H6=>(
zenon_notand _ _ (fun zenon_H5=>(zenon_H5 __C_1_2_2_2_51_LEMMA)) (fun
zenon_H4=>(zenon_H4 __C_1_2_2_2_91_LEMMA)) zenon_H6)) zenon_H8)))
zenon_G)))).
Qed.

            Theorem __C_1_2_2_2_LEMMA :
              ((abst_compatible (abst_voter va vb vc) (abst_voter vb va vc)) /\
                 (abst_compatible (abst_voter va vb vc)
                   (abst_voter vc va vb))).
            assert (__force_use_H222 := H222).
            assert (__force_use_H22 := H22).
            assert (__force_use_H2 := H2).
            apply for_zenon___C_1_2_2_2_LEMMA;
            auto.
            Qed.
            End __C_1_2_2_2.
(* File "vote.fcl", line 666, characters 17-55 *)
Theorem for_zenon___C_1_2_2_LEMMA:((abst_compatible (abst_voter va vb
vc) (abst_voter vb va vc))/\(abst_compatible (abst_voter va vb vc) (
abst_voter vc va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_imply _ _ (fun zenon_H5=>(zenon_imply _ _ (
fun zenon_H6=>(zenon_H6 zenon_H5)) (fun zenon_H4=>(zenon_G zenon_H4))
__C_1_2_2_2_LEMMA)) (fun zenon_H4=>(zenon_G zenon_H4))
__C_1_2_2_1_LEMMA)))).
Qed.

          Theorem __C_1_2_2_LEMMA :
            ((abst_compatible (abst_voter va vb vc) (abst_voter vb va vc)) /\
               (abst_compatible (abst_voter va vb vc) (abst_voter vc va vb))).
          assert (__force_use_H22 := H22).
          assert (__force_use_H2 := H2).
          apply for_zenon___C_1_2_2_LEMMA;
          auto.
          Qed.
          End __C_1_2_2.
(* File "vote.fcl", line 668, characters 15-53 *)
Theorem for_zenon___C_1_2_LEMMA:((abst_compatible (abst_voter va vb vc)
(abst_voter vb va vc))/\(abst_compatible (abst_voter va vb vc) (
abst_voter vc va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_imply _ _ (fun zenon_H5=>(zenon_imply _ _ (
fun zenon_H6=>(zenon_H6 zenon_H5)) (fun zenon_H4=>(zenon_G zenon_H4))
__C_1_2_2_LEMMA)) (fun zenon_H4=>(zenon_G zenon_H4)) __C_1_2_1_LEMMA)))).
Qed.

        Theorem __C_1_2_LEMMA :
          ((abst_compatible (abst_voter va vb vc) (abst_voter vb va vc)) /\
             (abst_compatible (abst_voter va vb vc) (abst_voter vc va vb))).
        assert (__force_use_H2 := H2).
        apply for_zenon___C_1_2_LEMMA;
        auto.
        Qed.
        End __C_1_2.
(* File "vote.fcl", line 670, characters 13-51 *)
Theorem for_zenon___C_1_LEMMA:((abst_compatible (abst_voter va vb vc) (
abst_voter vb va vc))/\(abst_compatible (abst_voter va vb vc) (
abst_voter vc va vb))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_imply _ _ (fun zenon_H5=>(zenon_imply _ _ (
fun zenon_H6=>(zenon_H6 zenon_H5)) (fun zenon_H4=>(zenon_G zenon_H4))
__C_1_2_LEMMA)) (fun zenon_H4=>(zenon_G zenon_H4)) __C_1_1_LEMMA)))).
Qed.

      Theorem __C_1_LEMMA :
        ((abst_compatible (abst_voter va vb vc) (abst_voter vb va vc)) /\
           (abst_compatible (abst_voter va vb vc) (abst_voter vc va vb))).
      apply for_zenon___C_1_LEMMA;
      auto.
      Qed.
      End __C_1.
(* File "vote.fcl", line 672, characters 11-43 *)
Theorem for_zenon_voter_independant_from_order_v1_v2:(forall va:_p_V_T,(
forall vb:_p_V_T,(forall vc:_p_V_T,((abst_compatible (abst_voter va vb
vc) (abst_voter vb va vc))/\(abst_compatible (abst_voter va vb vc) (
abst_voter vc va vb)))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G __C_1_LEMMA)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_voter_independant_from_order_v1_v2 :
      forall v1  v2  v3 : _p_V_T,
        (abst_compatible (abst_voter v1 v2 v3) (abst_voter v2 v1 v3)) /\
          (abst_compatible (abst_voter v1 v2 v3) (abst_voter v3 v1 v2)).
    assert (__force_use_p_E_T := _p_E_T).
    assert (__force_use_p_C_T := _p_C_T).
    assert (__force_use_p_V_T := _p_V_T).
    assert (__force_use_p_P_T := _p_P_T).
    assert (__force_use__p_E_equal := _p_E_equal).
    assert (__force_use__p_E_no_match := _p_E_no_match).
    assert (__force_use__p_E_partial_match := _p_E_partial_match).
    assert (__force_use__p_E_perfect_match := _p_E_perfect_match).
    assert (__force_use__p_E_range_match := _p_E_range_match).
    assert (__force_use__p_C_capt_1 := _p_C_capt_1).
    assert (__force_use__p_C_capt_2 := _p_C_capt_2).
    assert (__force_use__p_C_capt_3 := _p_C_capt_3).
    assert (__force_use__p_V_consistency_rule := _p_V_consistency_rule).
    assert (__force_use__p_V_consistency_rule_reflexive :=
      _p_V_consistency_rule_reflexive).
    assert (__force_use__p_V_consistency_rule_symmetric :=
      _p_V_consistency_rule_symmetric).
    assert (__force_use__p_P_constr := _p_P_constr).
    assert (__force_use__p_P_prj_b := _p_P_prj_b).
    assert (__force_use__p_P_valid := _p_P_valid).
    assert (__force_use__p_P_prj_b_is_snd_of_pair :=
      _p_P_prj_b_is_snd_of_pair).
    assert (__force_use__p_P_no_match_is_invalid :=
      _p_P_no_match_is_invalid).
    assert (__force_use__p_P_partial_match_is_valid :=
      _p_P_partial_match_is_valid).
    assert (__force_use__p_P_perfect_match_is_valid :=
      _p_P_perfect_match_is_valid).
    assert (__force_use__p_P_range_match_is_valid :=
      _p_P_range_match_is_valid).
    assert (__force_use_abst_consistency_rule_is_symmetric :=
      abst_consistency_rule_is_symmetric).
    assert (__force_use_abst_diag := abst_diag).
    assert (__force_use_abst_value := abst_value).
    assert (__force_use_abst_voter := abst_voter).
    assert (__force_use_abst_compatible := abst_compatible).
    assert (__force_use_abst_vote_match_c1 := abst_vote_match_c1).
    assert (__force_use_abst_vote_match_c2 := abst_vote_match_c2).
    assert (__force_use_abst_vote_match_c3 := abst_vote_match_c3).
    assert (__force_use_abst_vote_no_match := abst_vote_no_match).
    assert (__force_use_abst_vote_partial_c1 := abst_vote_partial_c1).
    assert (__force_use_abst_vote_partial_c2 := abst_vote_partial_c2).
    assert (__force_use_abst_vote_partial_c3 := abst_vote_partial_c3).
    assert (__force_use_abst_vote_perfect := abst_vote_perfect).
    apply for_zenon_voter_independant_from_order_v1_v2;
    auto.
    Qed.
    End Proof_of_voter_independant_from_order_v1_v2.
  
  Theorem voter_independant_from_order_v1_v2  (_p_E_T : Set) (_p_C_T : Set)
    (_p_V_T : Set) (_p_P_T : Set) (_p_E_equal :
    _p_E_T -> _p_E_T -> basics.bool__t) (_p_E_no_match : _p_E_T)
    (_p_E_partial_match : _p_E_T) (_p_E_perfect_match : _p_E_T)
    (_p_E_range_match : _p_E_T) (_p_C_capt_1 : _p_C_T) (_p_C_capt_2 : _p_C_T)
    (_p_C_capt_3 : _p_C_T) (_p_V_consistency_rule :
    _p_V_T -> _p_V_T -> basics.bool__t) (_p_V_consistency_rule_reflexive :
    forall a : _p_V_T, Is_true ((_p_V_consistency_rule a a)))
    (_p_V_consistency_rule_symmetric :
    forall a  b : _p_V_T,
      Is_true ((_p_V_consistency_rule a b)) ->
        Is_true ((_p_V_consistency_rule b a)))
    (_p_P_constr : _p_C_T -> _p_E_T -> _p_P_T) (_p_P_prj_b :
    _p_P_T -> _p_E_T) (_p_P_valid : _p_P_T -> basics.bool__t)
    (_p_P_prj_b_is_snd_of_pair :
    forall n1 : _p_C_T,
      forall n2 : _p_E_T,
        Is_true ((_p_E_equal (_p_P_prj_b (_p_P_constr n1 n2)) n2)))
    (_p_P_no_match_is_invalid :
    forall x : _p_P_T,
      Is_true ((_p_E_equal (_p_P_prj_b x) _p_E_no_match)) ->
        ~Is_true (((_p_P_valid x))))
    (_p_P_partial_match_is_valid :
    forall x : _p_P_T,
      Is_true ((_p_E_equal (_p_P_prj_b x) _p_E_partial_match)) ->
        Is_true ((_p_P_valid x)))
    (_p_P_perfect_match_is_valid :
    forall x : _p_P_T,
      Is_true ((_p_E_equal (_p_P_prj_b x) _p_E_perfect_match)) ->
        Is_true ((_p_P_valid x)))
    (_p_P_range_match_is_valid :
    forall x : _p_P_T,
      Is_true ((_p_E_equal (_p_P_prj_b x) _p_E_range_match)) ->
        Is_true ((_p_P_valid x)))
    (abst_consistency_rule_is_symmetric :
    forall v1  v2 : _p_V_T,
      Is_true ((_p_V_consistency_rule v1 v2)) ->
        Is_true ((_p_V_consistency_rule v2 v1)))
    (abst_diag : (Datatypes.prod _p_V_T _p_P_T) -> _p_P_T)
    (abst_value : (Datatypes.prod _p_V_T _p_P_T) -> _p_V_T)
    (abst_voter : _p_V_T ->
                    _p_V_T -> _p_V_T -> (Datatypes.prod _p_V_T _p_P_T))
    (abst_compatible := gen_vote.Gen_voter.compatible _p_V_T _p_P_T
    _p_V_consistency_rule _p_P_valid abst_diag abst_value)
    (abst_vote_match_c1 :
    forall v1  v2  v3 : _p_V_T,
      (~Is_true ((_p_V_consistency_rule v1 v2)) /\
         ~Is_true ((_p_V_consistency_rule v1 v3)) /\
           Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v2))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_1 _p_E_range_match))))))
    (abst_vote_match_c2 :
    forall v1  v2  v3 : _p_V_T,
      (~Is_true ((_p_V_consistency_rule v1 v2)) /\
         Is_true ((_p_V_consistency_rule v1 v3)) /\
           ~Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v3))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_2 _p_E_range_match))))))
    (abst_vote_match_c3 :
    forall v1  v2  v3 : _p_V_T,
      (Is_true ((_p_V_consistency_rule v1 v2)) /\
         ~Is_true ((_p_V_consistency_rule v1 v3)) /\
           ~Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v1))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_3 _p_E_range_match))))))
    (abst_vote_no_match :
    forall v1  v2  v3 : _p_V_T,
      (~Is_true ((_p_V_consistency_rule v1 v2)) /\
         ~Is_true ((_p_V_consistency_rule v1 v3)) /\
           ~Is_true ((_p_V_consistency_rule v2 v3))) ->
        Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                    (_p_P_constr _p_C_capt_1 _p_E_no_match)))))
    (abst_vote_partial_c1 :
    forall v1  v2  v3 : _p_V_T,
      (Is_true ((_p_V_consistency_rule v1 v2)) /\
         Is_true ((_p_V_consistency_rule v1 v3)) /\
           ~Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v1))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_1 _p_E_partial_match))))))
    (abst_vote_partial_c2 :
    forall v1  v2  v3 : _p_V_T,
      (Is_true ((_p_V_consistency_rule v1 v2)) /\
         ~Is_true ((_p_V_consistency_rule v1 v3)) /\
           Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v2))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_2 _p_E_partial_match))))))
    (abst_vote_partial_c3 :
    forall v1  v2  v3 : _p_V_T,
      (~Is_true ((_p_V_consistency_rule v1 v2)) /\
         Is_true ((_p_V_consistency_rule v1 v3)) /\
           Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v3))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_3 _p_E_partial_match))))))
    (abst_vote_perfect :
    forall v1  v2  v3 : _p_V_T,
      (Is_true ((_p_V_consistency_rule v1 v2)) /\
         Is_true ((_p_V_consistency_rule v2 v3)) /\
           Is_true ((_p_V_consistency_rule v1 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v1))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_1 _p_E_perfect_match)))))):
    forall v1  v2  v3 : _p_V_T,
      (abst_compatible (abst_voter v1 v2 v3) (abst_voter v2 v1 v3)) /\
        (abst_compatible (abst_voter v1 v2 v3) (abst_voter v3 v1 v2)).
  apply for_zenon_abstracted_voter_independant_from_order_v1_v2;
  auto.
  Qed.
  
  (* From species vote#Voteur. *)
  (* Section for proof of theorem 'voter_returns_an_input_value'. *)
  Section Proof_of_voter_returns_an_input_value.
    Variable _p_E_T : Set.
    Variable _p_C_T : Set.
    Variable _p_V_T : Set.
    Variable _p_P_T : Set.
    Variable _p_E_equal : _p_E_T -> _p_E_T -> basics.bool__t.
    Variable _p_E_no_match : _p_E_T.
    Variable _p_E_partial_match : _p_E_T.
    Variable _p_E_perfect_match : _p_E_T.
    Variable _p_E_range_match : _p_E_T.
    Variable _p_C_capt_1 : _p_C_T.
    Variable _p_C_capt_2 : _p_C_T.
    Variable _p_C_capt_3 : _p_C_T.
    Variable _p_V_consistency_rule : _p_V_T -> _p_V_T -> basics.bool__t.
    Variable _p_P_constr : _p_C_T -> _p_E_T -> _p_P_T.
    Variable _p_P_prj_b : _p_P_T -> _p_E_T.
    Variable _p_P_valid : _p_P_T -> basics.bool__t.
    Variable _p_P_prj_b_is_snd_of_pair :
      forall n1 : _p_C_T,
        forall n2 : _p_E_T,
          Is_true ((_p_E_equal (_p_P_prj_b (_p_P_constr n1 n2)) n2)).
    Variable _p_P_no_match_is_invalid :
      forall x : _p_P_T,
        Is_true ((_p_E_equal (_p_P_prj_b x) _p_E_no_match)) ->
          ~Is_true (((_p_P_valid x))).
    Variable abst_diag : (Datatypes.prod _p_V_T _p_P_T) -> _p_P_T.
    Let abst_state := state _p_E_T _p_P_T
    _p_P_prj_b.
    Variable abst_value : (Datatypes.prod _p_V_T _p_P_T) -> _p_V_T.
    Variable abst_voter : _p_V_T ->
                            _p_V_T ->
                              _p_V_T -> (Datatypes.prod _p_V_T _p_P_T).
    Hypothesis abst_vote_match_c1 :
      forall v1  v2  v3 : _p_V_T,
        (~Is_true ((_p_V_consistency_rule v1 v2)) /\
           ~Is_true ((_p_V_consistency_rule v1 v3)) /\
             Is_true ((_p_V_consistency_rule v2 v3))) ->
          (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                       v2))) /\
             Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                         (_p_P_constr _p_C_capt_1 _p_E_range_match))))).
    Hypothesis abst_vote_match_c2 :
      forall v1  v2  v3 : _p_V_T,
        (~Is_true ((_p_V_consistency_rule v1 v2)) /\
           Is_true ((_p_V_consistency_rule v1 v3)) /\
             ~Is_true ((_p_V_consistency_rule v2 v3))) ->
          (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                       v3))) /\
             Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                         (_p_P_constr _p_C_capt_2 _p_E_range_match))))).
    Hypothesis abst_vote_match_c3 :
      forall v1  v2  v3 : _p_V_T,
        (Is_true ((_p_V_consistency_rule v1 v2)) /\
           ~Is_true ((_p_V_consistency_rule v1 v3)) /\
             ~Is_true ((_p_V_consistency_rule v2 v3))) ->
          (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                       v1))) /\
             Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                         (_p_P_constr _p_C_capt_3 _p_E_range_match))))).
    Hypothesis abst_vote_no_match :
      forall v1  v2  v3 : _p_V_T,
        (~Is_true ((_p_V_consistency_rule v1 v2)) /\
           ~Is_true ((_p_V_consistency_rule v1 v3)) /\
             ~Is_true ((_p_V_consistency_rule v2 v3))) ->
          Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                      (_p_P_constr _p_C_capt_1 _p_E_no_match)))).
    Hypothesis abst_vote_partial_c1 :
      forall v1  v2  v3 : _p_V_T,
        (Is_true ((_p_V_consistency_rule v1 v2)) /\
           Is_true ((_p_V_consistency_rule v1 v3)) /\
             ~Is_true ((_p_V_consistency_rule v2 v3))) ->
          (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                       v1))) /\
             Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                         (_p_P_constr _p_C_capt_1 _p_E_partial_match))))).
    Hypothesis abst_vote_partial_c2 :
      forall v1  v2  v3 : _p_V_T,
        (Is_true ((_p_V_consistency_rule v1 v2)) /\
           ~Is_true ((_p_V_consistency_rule v1 v3)) /\
             Is_true ((_p_V_consistency_rule v2 v3))) ->
          (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                       v2))) /\
             Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                         (_p_P_constr _p_C_capt_2 _p_E_partial_match))))).
    Hypothesis abst_vote_partial_c3 :
      forall v1  v2  v3 : _p_V_T,
        (~Is_true ((_p_V_consistency_rule v1 v2)) /\
           Is_true ((_p_V_consistency_rule v1 v3)) /\
             Is_true ((_p_V_consistency_rule v2 v3))) ->
          (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                       v3))) /\
             Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                         (_p_P_constr _p_C_capt_3 _p_E_partial_match))))).
    Hypothesis abst_vote_perfect :
      forall v1  v2  v3 : _p_V_T,
        (Is_true ((_p_V_consistency_rule v1 v2)) /\
           Is_true ((_p_V_consistency_rule v2 v3)) /\
             Is_true ((_p_V_consistency_rule v1 v3))) ->
          (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                       v1))) /\
             Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                         (_p_P_constr _p_C_capt_1 _p_E_perfect_match))))).
    Section __D_1.
      Variable va : _p_V_T.
      Variable vb : _p_V_T.
      Variable vc : _p_V_T.
      Section __D_1_1.
        Variable H1 : Is_true ((_p_V_consistency_rule va vb)).
        Section __D_1_1_1.
          Variable H11 : Is_true ((_p_V_consistency_rule vb vc)).
          Section __D_1_1_1_1.
            Variable H111 : Is_true ((_p_V_consistency_rule va vc)).
(* File "vote.fcl", line 179, characters 9-58 *)
Theorem for_zenon___D_1_1_1_1_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) va)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((
Is_true (_p_V_consistency_rule v2 v3))/\(Is_true (_p_V_consistency_rule
v1 v3))))->((Is_true (basics._equal_ _ (abst_value (abst_voter v1 v2 v3)
) v1))/\(Is_true (basics._equal_ _ (abst_diag (abst_voter v1 v2 v3)) (
_p_P_constr _p_C_capt_1 _p_E_perfect_match)))))))) va (fun zenon_Hf=>(
zenon_all _p_V_T (fun v2:_p_V_T=>(forall v3:_p_V_T,(((Is_true (
_p_V_consistency_rule va v2))/\((Is_true (_p_V_consistency_rule v2 v3))
/\(Is_true (_p_V_consistency_rule va v3))))->((Is_true (basics._equal_
_ (abst_value (abst_voter va v2 v3)) va))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_perfect_match))))))) vb (fun zenon_He=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule va vb))/\((Is_true (
_p_V_consistency_rule vb v3))/\(Is_true (_p_V_consistency_rule va v3))))
->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) va))/\(
Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_1 _p_E_perfect_match)))))) vc (fun zenon_Hd=>(
zenon_imply _ _ (fun zenon_Hc=>(zenon_notand _ _ (fun zenon_Hb=>(
zenon_Hb H1)) (fun zenon_Ha=>(zenon_notand _ _ (fun zenon_H9=>(zenon_H9
H11)) (fun zenon_H8=>(zenon_H8 H111)) zenon_Ha)) zenon_Hc)) (fun
zenon_H7=>(zenon_and _ _ (fun zenon_H5 zenon_H6=>(zenon_G zenon_H5))
zenon_H7)) zenon_Hd)) zenon_He)) zenon_Hf)) abst_vote_perfect)))).
Qed.

            Theorem __D_1_1_1_1_LEMMA :
              Is_true ((((basics._equal_ _)
                          (abst_value (abst_voter va vb vc)) va))).
            assert (__force_use_H111 := H111).
            assert (__force_use_H11 := H11).
            assert (__force_use_H1 := H1).
            apply for_zenon___D_1_1_1_1_LEMMA;
            auto.
            Qed.
            End __D_1_1_1_1.
          Section __D_1_1_1_2.
            Variable H112 : ~Is_true (((_p_V_consistency_rule va vc))).
(* File "vote.fcl", line 183, characters 9-61 *)
Theorem for_zenon___D_1_1_1_2_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vb)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((~
(Is_true (_p_V_consistency_rule v1 v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_partial_match)))))))) va (fun zenon_H10=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule va v2))/\((
~(Is_true (_p_V_consistency_rule va v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_partial_match))))))) vb (fun zenon_Hf=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule va vb))/\((~(Is_true (
_p_V_consistency_rule va v3)))/\(Is_true (_p_V_consistency_rule vb v3)))
)->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) vb))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_2 _p_E_partial_match)))))) vc (fun zenon_He=>(
zenon_imply _ _ (fun zenon_Hd=>(zenon_notand _ _ (fun zenon_Hc=>(
zenon_Hc H1)) (fun zenon_Hb=>(zenon_notand _ _ (fun zenon_Ha=>(zenon_Ha
(fun zenon_H9=>(H112 zenon_H9)))) (fun zenon_H8=>(zenon_H8 H11))
zenon_Hb)) zenon_Hd)) (fun zenon_H7=>(zenon_and _ _ (fun zenon_H5
zenon_H6=>(zenon_G zenon_H5)) zenon_H7)) zenon_He)) zenon_Hf))
zenon_H10)) abst_vote_partial_c2)))).
Qed.

            Theorem __D_1_1_1_2_LEMMA :
              Is_true ((((basics._equal_ _)
                          (abst_value (abst_voter va vb vc)) vb))).
            assert (__force_use_H112 := H112).
            assert (__force_use_H11 := H11).
            assert (__force_use_H1 := H1).
            apply for_zenon___D_1_1_1_2_LEMMA;
            auto.
            Qed.
            End __D_1_1_1_2.
(* File "vote.fcl", line 184, characters 9-22 *)
Theorem for_zenon___D_1_1_1_LEMMA:((Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) va))\/((Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vb))\/(Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vc)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notor _ _ (fun zenon_H4 zenon_Ha=>(
zenon_notor _ _ (fun zenon_H6 zenon_H9=>(zenon_imply _ _ (fun zenon_H7=>
(zenon_imply _ _ (fun zenon_H8=>(zenon_H8 zenon_H7)) (fun zenon_H5=>(
zenon_H6 zenon_H5)) __D_1_1_1_2_LEMMA)) (fun zenon_H3=>(zenon_H4
zenon_H3)) __D_1_1_1_1_LEMMA)) zenon_Ha)) zenon_G)))).
Qed.

          Theorem __D_1_1_1_LEMMA :
            (Is_true ((((basics._equal_ _) (abst_value (abst_voter va vb vc))
                         va))) \/
               Is_true ((((basics._equal_ _)
                           (abst_value (abst_voter va vb vc)) vb))) \/
                 Is_true ((((basics._equal_ _)
                             (abst_value (abst_voter va vb vc)) vc)))).
          assert (__force_use_H11 := H11).
          assert (__force_use_H1 := H1).
          apply for_zenon___D_1_1_1_LEMMA;
          auto.
          Qed.
          End __D_1_1_1.
        Section __D_1_1_2.
          Variable H12 : ~Is_true (((_p_V_consistency_rule vb vc))).
          Section __D_1_1_2_1.
            Variable H121 : Is_true ((_p_V_consistency_rule va vc)).
(* File "vote.fcl", line 198, characters 9-61 *)
Theorem for_zenon___D_1_1_2_1_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) va)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((
Is_true (_p_V_consistency_rule v1 v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v1))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_partial_match)))))))) va (fun zenon_H10=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule va v2))/\((
Is_true (_p_V_consistency_rule va v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) va))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_partial_match))))))) vb (fun zenon_Hf=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule va vb))/\((Is_true (
_p_V_consistency_rule va v3))/\(~(Is_true (_p_V_consistency_rule vb v3))
)))->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) va))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_1 _p_E_partial_match)))))) vc (fun zenon_He=>(
zenon_imply _ _ (fun zenon_Hd=>(zenon_notand _ _ (fun zenon_Hc=>(
zenon_Hc H1)) (fun zenon_Hb=>(zenon_notand _ _ (fun zenon_Ha=>(zenon_Ha
H121)) (fun zenon_H9=>(zenon_H9 (fun zenon_H8=>(H12 zenon_H8))))
zenon_Hb)) zenon_Hd)) (fun zenon_H7=>(zenon_and _ _ (fun zenon_H5
zenon_H6=>(zenon_G zenon_H5)) zenon_H7)) zenon_He)) zenon_Hf))
zenon_H10)) abst_vote_partial_c1)))).
Qed.

            Theorem __D_1_1_2_1_LEMMA :
              Is_true ((((basics._equal_ _)
                          (abst_value (abst_voter va vb vc)) va))).
            assert (__force_use_H121 := H121).
            assert (__force_use_H12 := H12).
            assert (__force_use_H1 := H1).
            apply for_zenon___D_1_1_2_1_LEMMA;
            auto.
            Qed.
            End __D_1_1_2_1.
          Section __D_1_1_2_2.
            Variable H122 : ~Is_true (((_p_V_consistency_rule va vc))).
(* File "vote.fcl", line 203, characters 9-59 *)
Theorem for_zenon___D_1_1_2_2_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) va)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule v1 v2))/\((~
(Is_true (_p_V_consistency_rule v1 v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v1))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_range_match)))))))) va (fun zenon_H11=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((Is_true (_p_V_consistency_rule va v2))/\((
~(Is_true (_p_V_consistency_rule va v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) va))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_range_match))))))) vb (fun zenon_H10=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((Is_true (_p_V_consistency_rule va vb))/\((~(Is_true (
_p_V_consistency_rule va v3)))/\(~(Is_true (_p_V_consistency_rule vb v3)
))))->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) va)
)/\(Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_3 _p_E_range_match)))))) vc (fun zenon_Hf=>(
zenon_imply _ _ (fun zenon_He=>(zenon_notand _ _ (fun zenon_Hd=>(
zenon_Hd H1)) (fun zenon_Hc=>(zenon_notand _ _ (fun zenon_Hb=>(zenon_Hb
(fun zenon_Ha=>(H122 zenon_Ha)))) (fun zenon_H9=>(zenon_H9 (fun
zenon_H8=>(H12 zenon_H8)))) zenon_Hc)) zenon_He)) (fun zenon_H7=>(
zenon_and _ _ (fun zenon_H5 zenon_H6=>(zenon_G zenon_H5)) zenon_H7))
zenon_Hf)) zenon_H10)) zenon_H11)) abst_vote_match_c3)))).
Qed.

            Theorem __D_1_1_2_2_LEMMA :
              Is_true ((((basics._equal_ _)
                          (abst_value (abst_voter va vb vc)) va))).
            assert (__force_use_H122 := H122).
            assert (__force_use_H12 := H12).
            assert (__force_use_H1 := H1).
            apply for_zenon___D_1_1_2_2_LEMMA;
            auto.
            Qed.
            End __D_1_1_2_2.
(* File "vote.fcl", line 204, characters 9-22 *)
Theorem for_zenon___D_1_1_2_LEMMA:((Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) va))\/((Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vb))\/(Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vc)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notor _ _ (fun zenon_H4 zenon_H7=>(
zenon_imply _ _ (fun zenon_H5=>(zenon_imply _ _ (fun zenon_H6=>(
zenon_H6 zenon_H5)) (fun zenon_H3=>(zenon_H4 zenon_H3))
__D_1_1_2_2_LEMMA)) (fun zenon_H3=>(zenon_H4 zenon_H3))
__D_1_1_2_1_LEMMA)) zenon_G)))).
Qed.

          Theorem __D_1_1_2_LEMMA :
            (Is_true ((((basics._equal_ _) (abst_value (abst_voter va vb vc))
                         va))) \/
               Is_true ((((basics._equal_ _)
                           (abst_value (abst_voter va vb vc)) vb))) \/
                 Is_true ((((basics._equal_ _)
                             (abst_value (abst_voter va vb vc)) vc)))).
          assert (__force_use_H12 := H12).
          assert (__force_use_H1 := H1).
          apply for_zenon___D_1_1_2_LEMMA;
          auto.
          Qed.
          End __D_1_1_2.
(* File "vote.fcl", line 206, characters 5-18 *)
Theorem for_zenon___D_1_1_LEMMA:((Is_true (basics._equal_ _ (abst_value
(abst_voter va vb vc)) va))\/((Is_true (basics._equal_ _ (abst_value (
abst_voter va vb vc)) vb))\/((Is_true (basics._equal_ _ (abst_value (
abst_voter va vb vc)) vc))\/(~(Is_true (_p_P_valid (abst_diag (
abst_voter va vb vc)))))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notor _ _ (fun zenon_H9 zenon_H10=>(
zenon_notor _ _ (fun zenon_H6 zenon_Hf=>(zenon_notor _ _ (fun zenon_H4
zenon_He=>(zenon_imply _ _ (fun zenon_Hc=>(zenon_imply _ _ (fun
zenon_Hd=>(zenon_Hd (fun zenon_Hb=>(zenon_Hc zenon_Hb)))) (fun
zenon_Ha=>(zenon_or _ _ (fun zenon_H8=>(zenon_H9 zenon_H8)) (fun
zenon_H7=>(zenon_or _ _ (fun zenon_H5=>(zenon_H6 zenon_H5)) (fun
zenon_H3=>(zenon_H4 zenon_H3)) zenon_H7)) zenon_Ha)) __D_1_1_2_LEMMA)) (
fun zenon_Ha=>(zenon_or _ _ (fun zenon_H8=>(zenon_H9 zenon_H8)) (fun
zenon_H7=>(zenon_or _ _ (fun zenon_H5=>(zenon_H6 zenon_H5)) (fun
zenon_H3=>(zenon_H4 zenon_H3)) zenon_H7)) zenon_Ha)) __D_1_1_1_LEMMA))
zenon_Hf)) zenon_H10)) zenon_G)))).
Qed.

        Theorem __D_1_1_LEMMA :
          (Is_true ((((basics._equal_ _) (abst_value (abst_voter va vb vc))
                       va))) \/
             Is_true ((((basics._equal_ _) (abst_value (abst_voter va vb vc))
                         vb))) \/
               Is_true ((((basics._equal_ _)
                           (abst_value (abst_voter va vb vc)) vc))) \/
                 (~Is_true (((_p_P_valid (abst_diag (abst_voter va vb vc))))))).
        assert (__force_use_H1 := H1).
        apply for_zenon___D_1_1_LEMMA;
        auto.
        Qed.
        End __D_1_1.
      Section __D_1_2.
        Variable H2 : ~Is_true (((_p_V_consistency_rule va vb))).
        Section __D_1_2_1.
          Variable H21 : Is_true ((_p_V_consistency_rule vb vc)).
          Section __D_1_2_1_1.
            Variable H211 : Is_true ((_p_V_consistency_rule va vc)).
(* File "vote.fcl", line 229, characters 9-61 *)
Theorem for_zenon___D_1_2_1_1_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vc)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((Is_true (_p_V_consistency_rule v1 v3))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_partial_match)))))))) va (fun zenon_H10=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule va v2)))
/\((Is_true (_p_V_consistency_rule va v3))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_3
_p_E_partial_match))))))) vb (fun zenon_Hf=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule va vb)))/\((Is_true (
_p_V_consistency_rule va v3))/\(Is_true (_p_V_consistency_rule vb v3))))
->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) v3))/\(
Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_3 _p_E_partial_match)))))) vc (fun zenon_He=>(
zenon_imply _ _ (fun zenon_Hd=>(zenon_notand _ _ (fun zenon_Hc=>(
zenon_Hc (fun zenon_Hb=>(H2 zenon_Hb)))) (fun zenon_Ha=>(zenon_notand _
_ (fun zenon_H9=>(zenon_H9 H211)) (fun zenon_H8=>(zenon_H8 H21))
zenon_Ha)) zenon_Hd)) (fun zenon_H7=>(zenon_and _ _ (fun zenon_H5
zenon_H6=>(zenon_G zenon_H5)) zenon_H7)) zenon_He)) zenon_Hf))
zenon_H10)) abst_vote_partial_c3)))).
Qed.

            Theorem __D_1_2_1_1_LEMMA :
              Is_true ((((basics._equal_ _)
                          (abst_value (abst_voter va vb vc)) vc))).
            assert (__force_use_H211 := H211).
            assert (__force_use_H21 := H21).
            assert (__force_use_H2 := H2).
            apply for_zenon___D_1_2_1_1_LEMMA;
            auto.
            Qed.
            End __D_1_2_1_1.
          Section __D_1_2_1_2.
            Variable H212 : ~Is_true (((_p_V_consistency_rule va vc))).
(* File "vote.fcl", line 234, characters 9-59 *)
Theorem for_zenon___D_1_2_1_2_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vb)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((~(Is_true (_p_V_consistency_rule v1 v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_range_match)))))))) va (fun zenon_H11=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule va v2)))
/\((~(Is_true (_p_V_consistency_rule va v3)))/\(Is_true (
_p_V_consistency_rule v2 v3))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) v2))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_1
_p_E_range_match))))))) vb (fun zenon_H10=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule va vb)))/\((~(Is_true (
_p_V_consistency_rule va v3)))/\(Is_true (_p_V_consistency_rule vb v3)))
)->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) vb))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_1 _p_E_range_match)))))) vc (fun zenon_Hf=>(
zenon_imply _ _ (fun zenon_He=>(zenon_notand _ _ (fun zenon_Hd=>(
zenon_Hd (fun zenon_Hc=>(H2 zenon_Hc)))) (fun zenon_Hb=>(zenon_notand _
_ (fun zenon_Ha=>(zenon_Ha (fun zenon_H9=>(H212 zenon_H9)))) (fun
zenon_H8=>(zenon_H8 H21)) zenon_Hb)) zenon_He)) (fun zenon_H7=>(
zenon_and _ _ (fun zenon_H5 zenon_H6=>(zenon_G zenon_H5)) zenon_H7))
zenon_Hf)) zenon_H10)) zenon_H11)) abst_vote_match_c1)))).
Qed.

            Theorem __D_1_2_1_2_LEMMA :
              Is_true ((((basics._equal_ _)
                          (abst_value (abst_voter va vb vc)) vb))).
            assert (__force_use_H212 := H212).
            assert (__force_use_H21 := H21).
            assert (__force_use_H2 := H2).
            apply for_zenon___D_1_2_1_2_LEMMA;
            auto.
            Qed.
            End __D_1_2_1_2.
(* File "vote.fcl", line 235, characters 9-22 *)
Theorem for_zenon___D_1_2_1_LEMMA:((Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) va))\/((Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vb))\/(Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vc)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notor _ _ (fun zenon_Ha zenon_H9=>(
zenon_notor _ _ (fun zenon_H6 zenon_H4=>(zenon_imply _ _ (fun zenon_H7=>
(zenon_imply _ _ (fun zenon_H8=>(zenon_H8 zenon_H7)) (fun zenon_H5=>(
zenon_H6 zenon_H5)) __D_1_2_1_2_LEMMA)) (fun zenon_H3=>(zenon_H4
zenon_H3)) __D_1_2_1_1_LEMMA)) zenon_H9)) zenon_G)))).
Qed.

          Theorem __D_1_2_1_LEMMA :
            (Is_true ((((basics._equal_ _) (abst_value (abst_voter va vb vc))
                         va))) \/
               Is_true ((((basics._equal_ _)
                           (abst_value (abst_voter va vb vc)) vb))) \/
                 Is_true ((((basics._equal_ _)
                             (abst_value (abst_voter va vb vc)) vc)))).
          assert (__force_use_H21 := H21).
          assert (__force_use_H2 := H2).
          apply for_zenon___D_1_2_1_LEMMA;
          auto.
          Qed.
          End __D_1_2_1.
        Section __D_1_2_2.
          Variable H22 : ~Is_true (((_p_V_consistency_rule vb vc))).
          Section __D_1_2_2_1.
            Variable H221 : Is_true ((_p_V_consistency_rule va vc)).
(* File "vote.fcl", line 249, characters 9-59 *)
Theorem for_zenon___D_1_2_2_1_LEMMA:(Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vc)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((Is_true (_p_V_consistency_rule v1 v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter v1 v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_range_match)))))))) va (fun zenon_H11=>(zenon_all _p_V_T (fun v2
:_p_V_T=>(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule va v2)))
/\((Is_true (_p_V_consistency_rule va v3))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->((Is_true (basics._equal_ _ (
abst_value (abst_voter va v2 v3)) v3))/\(Is_true (basics._equal_ _ (
abst_diag (abst_voter va v2 v3)) (_p_P_constr _p_C_capt_2
_p_E_range_match))))))) vb (fun zenon_H10=>(zenon_all _p_V_T (fun v3
:_p_V_T=>(((~(Is_true (_p_V_consistency_rule va vb)))/\((Is_true (
_p_V_consistency_rule va v3))/\(~(Is_true (_p_V_consistency_rule vb v3))
)))->((Is_true (basics._equal_ _ (abst_value (abst_voter va vb v3)) v3))
/\(Is_true (basics._equal_ _ (abst_diag (abst_voter va vb v3)) (
_p_P_constr _p_C_capt_2 _p_E_range_match)))))) vc (fun zenon_Hf=>(
zenon_imply _ _ (fun zenon_He=>(zenon_notand _ _ (fun zenon_Hd=>(
zenon_Hd (fun zenon_Hc=>(H2 zenon_Hc)))) (fun zenon_Hb=>(zenon_notand _
_ (fun zenon_Ha=>(zenon_Ha H221)) (fun zenon_H9=>(zenon_H9 (fun
zenon_H8=>(H22 zenon_H8)))) zenon_Hb)) zenon_He)) (fun zenon_H7=>(
zenon_and _ _ (fun zenon_H5 zenon_H6=>(zenon_G zenon_H5)) zenon_H7))
zenon_Hf)) zenon_H10)) zenon_H11)) abst_vote_match_c2)))).
Qed.

            Theorem __D_1_2_2_1_LEMMA :
              Is_true ((((basics._equal_ _)
                          (abst_value (abst_voter va vb vc)) vc))).
            assert (__force_use_H221 := H221).
            assert (__force_use_H22 := H22).
            assert (__force_use_H2 := H2).
            apply for_zenon___D_1_2_2_1_LEMMA;
            auto.
            Qed.
            End __D_1_2_2_1.
          Section __D_1_2_2_2.
            Variable H222 : ~Is_true (((_p_V_consistency_rule va vc))).
            Section __D_1_2_2_2_1.
(* File "vote.fcl", line 255, characters 11-61 *)
Theorem for_zenon___D_1_2_2_2_1_LEMMA:(Is_true (basics._equal_ _ (
abst_diag (abst_voter va vb vc)) (_p_P_constr _p_C_capt_1 _p_E_no_match)
)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_V_T (fun v1:_p_V_T=>(forall v2
:_p_V_T,(forall v3:_p_V_T,(((~(Is_true (_p_V_consistency_rule v1 v2)))
/\((~(Is_true (_p_V_consistency_rule v1 v3)))/\(~(Is_true (
_p_V_consistency_rule v2 v3)))))->(Is_true (basics._equal_ _ (abst_diag
(abst_voter v1 v2 v3)) (_p_P_constr _p_C_capt_1 _p_E_no_match))))))) va
(fun zenon_H10=>(zenon_all _p_V_T (fun v2:_p_V_T=>(forall v3:_p_V_T,(((~
(Is_true (_p_V_consistency_rule va v2)))/\((~(Is_true (
_p_V_consistency_rule va v3)))/\(~(Is_true (_p_V_consistency_rule v2 v3)
))))->(Is_true (basics._equal_ _ (abst_diag (abst_voter va v2 v3)) (
_p_P_constr _p_C_capt_1 _p_E_no_match)))))) vb (fun zenon_Hf=>(
zenon_all _p_V_T (fun v3:_p_V_T=>(((~(Is_true (_p_V_consistency_rule va
vb)))/\((~(Is_true (_p_V_consistency_rule va v3)))/\(~(Is_true (
_p_V_consistency_rule vb v3)))))->(Is_true (basics._equal_ _ (abst_diag
(abst_voter va vb v3)) (_p_P_constr _p_C_capt_1 _p_E_no_match))))) vc (
fun zenon_He=>(zenon_imply _ _ (fun zenon_Hd=>(zenon_notand _ _ (fun
zenon_Hc=>(zenon_Hc (fun zenon_Hb=>(H2 zenon_Hb)))) (fun zenon_Ha=>(
zenon_notand _ _ (fun zenon_H9=>(zenon_H9 (fun zenon_H8=>(H222 zenon_H8)
))) (fun zenon_H7=>(zenon_H7 (fun zenon_H6=>(H22 zenon_H6)))) zenon_Ha))
 zenon_Hd)) (fun zenon_H5=>(zenon_G zenon_H5)) zenon_He)) zenon_Hf))
zenon_H10)) abst_vote_no_match)))).
Qed.

              Theorem __D_1_2_2_2_1_LEMMA :
                Is_true ((((basics._equal_ _)
                            (abst_diag (abst_voter va vb vc))
                            (_p_P_constr _p_C_capt_1 _p_E_no_match)))).
              assert (__force_use_H222 := H222).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___D_1_2_2_2_1_LEMMA;
              auto.
              Qed.
              End __D_1_2_2_2_1.
            Section __D_1_2_2_2_2.
(* File "vote.fcl", line 257, characters 11-75 *)
Theorem for_zenon___D_1_2_2_2_2_LEMMA:(Is_true (_p_E_equal (abst_state (
abst_diag (abst_voter va vb vc))) _p_E_no_match)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(coq_builtins.zenon_syntactic_equal
zenon_focal_eqdec _ (abst_diag (abst_voter va vb vc)) (_p_P_constr
_p_C_capt_1 _p_E_no_match) (fun zenon_H6=>(zenon_all _p_C_T (fun n1
:_p_C_T=>(forall n2:_p_E_T,(Is_true (_p_E_equal (_p_P_prj_b (
_p_P_constr n1 n2)) n2)))) _p_C_capt_1 (fun zenon_H9=>(zenon_all _p_E_T
(fun n2:_p_E_T=>(Is_true (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 n2)) n2))) _p_E_no_match (fun zenon_H3=>(zenon_subst _ (fun
zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (_p_P_prj_b (_p_P_constr
_p_C_capt_1 _p_E_no_match)) _p_E_no_match) (_p_E_equal (abst_state (
abst_diag (abst_voter va vb vc))) _p_E_no_match) (fun zenon_H4=>(
zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg _p_E_no_match) = (
_p_E_equal (abst_state (abst_diag (abst_voter va vb vc))) _p_E_no_match)
))) (_p_P_prj_b (_p_P_constr _p_C_capt_1 _p_E_no_match)) (abst_state (
abst_diag (abst_voter va vb vc))) (fun zenon_H8=>(let zenon_H5
:=zenon_H8 in (zenon_subst _ (fun zenon_Vh=>(~((_p_P_prj_b zenon_Vh) = (
_p_P_prj_b (abst_diag (abst_voter va vb vc)))))) (_p_P_constr
_p_C_capt_1 _p_E_no_match) (abst_diag (abst_voter va vb vc)) (fun
zenon_H7=>(zenon_eqsym _ (abst_diag (abst_voter va vb vc)) (_p_P_constr
_p_C_capt_1 _p_E_no_match) zenon_H6 zenon_H7)) (zenon_notnot _ (
refl_equal (_p_P_prj_b (abst_diag (abst_voter va vb vc))))) zenon_H5)))
(zenon_notnot _ (refl_equal (_p_E_equal (abst_state (abst_diag (
abst_voter va vb vc))) _p_E_no_match))) zenon_H4)) zenon_G zenon_H3))
zenon_H9)) _p_P_prj_b_is_snd_of_pair)) __D_1_2_2_2_1_LEMMA)))).
Qed.

              Theorem __D_1_2_2_2_2_LEMMA :
                Is_true (((_p_E_equal
                            (abst_state (abst_diag (abst_voter va vb vc)))
                            _p_E_no_match))).
              assert (__force_use_H222 := H222).
              assert (__force_use_H22 := H22).
              assert (__force_use_H2 := H2).
              apply for_zenon___D_1_2_2_2_2_LEMMA;
              auto.
              Qed.
              End __D_1_2_2_2_2.
(* File "vote.fcl", line 258, character 20, line 259, character 50 *)
Theorem for_zenon___D_1_2_2_2_LEMMA:(~(Is_true (_p_P_valid (abst_diag (
abst_voter va vb vc))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G (fun zenon_H3=>(zenon_all _p_P_T (fun x
:_p_P_T=>((Is_true (_p_E_equal (_p_P_prj_b x) _p_E_no_match))->(~(
Is_true (_p_P_valid x))))) (abst_diag (abst_voter va vb vc)) (fun
zenon_H9=>(zenon_imply _ _ (fun zenon_H5=>(zenon_subst _ (fun zenon_Vf=>
(Is_true zenon_Vf)) (_p_E_equal (abst_state (abst_diag (abst_voter va
vb vc))) _p_E_no_match) (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter
va vb vc))) _p_E_no_match) (fun zenon_H6=>(zenon_subst _ (fun zenon_Vg=>
(~((_p_E_equal zenon_Vg _p_E_no_match) = (_p_E_equal (_p_P_prj_b (
abst_diag (abst_voter va vb vc))) _p_E_no_match)))) (abst_state (
abst_diag (abst_voter va vb vc))) (_p_P_prj_b (abst_diag (abst_voter va
vb vc))) (fun zenon_H8=>(let zenon_H7:=zenon_H8 in (zenon_noteq _ (
_p_P_prj_b (abst_diag (abst_voter va vb vc))) zenon_H7))) (zenon_notnot
_ (refl_equal (_p_E_equal (_p_P_prj_b (abst_diag (abst_voter va vb vc)))
 _p_E_no_match))) zenon_H6)) zenon_H5 __D_1_2_2_2_2_LEMMA)) (fun
zenon_H4=>(zenon_H4 zenon_H3)) zenon_H9)) _p_P_no_match_is_invalid)))))).
Qed.

            Theorem __D_1_2_2_2_LEMMA :
              (~Is_true (((_p_P_valid (abst_diag (abst_voter va vb vc)))))).
            assert (__force_use_H222 := H222).
            assert (__force_use_H22 := H22).
            assert (__force_use_H2 := H2).
            apply for_zenon___D_1_2_2_2_LEMMA;
            auto.
            Qed.
            End __D_1_2_2_2.
(* File "vote.fcl", line 260, characters 9-22 *)
Theorem for_zenon___D_1_2_2_LEMMA:((Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) va))\/((Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vb))\/((Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vc))\/(~(Is_true (_p_P_valid (
abst_diag (abst_voter va vb vc)))))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notor _ _ (fun zenon_Hd zenon_Hc=>(
zenon_notor _ _ (fun zenon_Hb zenon_Ha=>(zenon_notor _ _ (fun zenon_H4
zenon_H9=>(zenon_H9 (fun zenon_H5=>(zenon_imply _ _ (fun zenon_H7=>(
zenon_imply _ _ (fun zenon_H8=>(zenon_H8 zenon_H7)) (fun zenon_H6=>(
zenon_H6 zenon_H5)) __D_1_2_2_2_LEMMA)) (fun zenon_H3=>(zenon_H4
zenon_H3)) __D_1_2_2_1_LEMMA)))) zenon_Ha)) zenon_Hc)) zenon_G)))).
Qed.

          Theorem __D_1_2_2_LEMMA :
            (Is_true ((((basics._equal_ _) (abst_value (abst_voter va vb vc))
                         va))) \/
               Is_true ((((basics._equal_ _)
                           (abst_value (abst_voter va vb vc)) vb))) \/
                 Is_true ((((basics._equal_ _)
                             (abst_value (abst_voter va vb vc)) vc))) \/
                   (~Is_true (((_p_P_valid (abst_diag (abst_voter va vb vc))))))).
          assert (__force_use_H22 := H22).
          assert (__force_use_H2 := H2).
          apply for_zenon___D_1_2_2_LEMMA;
          auto.
          Qed.
          End __D_1_2_2.
(* File "vote.fcl", line 262, characters 7-20 *)
Theorem for_zenon___D_1_2_LEMMA:((Is_true (basics._equal_ _ (abst_value
(abst_voter va vb vc)) va))\/((Is_true (basics._equal_ _ (abst_value (
abst_voter va vb vc)) vb))\/((Is_true (basics._equal_ _ (abst_value (
abst_voter va vb vc)) vc))\/(~(Is_true (_p_P_valid (abst_diag (
abst_voter va vb vc)))))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notor _ _ (fun zenon_H9 zenon_H15=>(
zenon_notor _ _ (fun zenon_H6 zenon_H14=>(zenon_notor _ _ (fun zenon_H4
zenon_H13=>(zenon_H13 (fun zenon_Hb=>(zenon_imply _ _ (fun zenon_H11=>(
zenon_imply _ _ (fun zenon_H12=>(zenon_H12 (fun zenon_H10=>(zenon_H11
zenon_H10)))) (fun zenon_Hf=>(zenon_or _ _ (fun zenon_H8=>(zenon_H9
zenon_H8)) (fun zenon_He=>(zenon_or _ _ (fun zenon_H5=>(zenon_H6
zenon_H5)) (fun zenon_Hd=>(zenon_or _ _ (fun zenon_H3=>(zenon_H4
zenon_H3)) (fun zenon_Hc=>(zenon_Hc zenon_Hb)) zenon_Hd)) zenon_He))
zenon_Hf)) __D_1_2_2_LEMMA)) (fun zenon_Ha=>(zenon_or _ _ (fun
zenon_H8=>(zenon_H9 zenon_H8)) (fun zenon_H7=>(zenon_or _ _ (fun
zenon_H5=>(zenon_H6 zenon_H5)) (fun zenon_H3=>(zenon_H4 zenon_H3))
zenon_H7)) zenon_Ha)) __D_1_2_1_LEMMA)))) zenon_H14)) zenon_H15))
zenon_G)))).
Qed.

        Theorem __D_1_2_LEMMA :
          (Is_true ((((basics._equal_ _) (abst_value (abst_voter va vb vc))
                       va))) \/
             Is_true ((((basics._equal_ _) (abst_value (abst_voter va vb vc))
                         vb))) \/
               Is_true ((((basics._equal_ _)
                           (abst_value (abst_voter va vb vc)) vc))) \/
                 (~Is_true (((_p_P_valid (abst_diag (abst_voter va vb vc))))))).
        assert (__force_use_H2 := H2).
        apply for_zenon___D_1_2_LEMMA;
        auto.
        Qed.
        End __D_1_2.
(* File "vote.fcl", line 264, characters 5-18 *)
Theorem for_zenon___D_1_LEMMA:((Is_true (basics._equal_ _ (abst_value (
abst_voter va vb vc)) va))\/((Is_true (basics._equal_ _ (abst_value (
abst_voter va vb vc)) vb))\/((Is_true (basics._equal_ _ (abst_value (
abst_voter va vb vc)) vc))\/(~(Is_true (_p_P_valid (abst_diag (
abst_voter va vb vc)))))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notor _ _ (fun zenon_Hc zenon_H13=>(
zenon_notor _ _ (fun zenon_H9 zenon_H12=>(zenon_notor _ _ (fun zenon_H6
zenon_H11=>(zenon_H11 (fun zenon_H3=>(zenon_imply _ _ (fun zenon_Hf=>(
zenon_imply _ _ (fun zenon_H10=>(zenon_H10 (fun zenon_He=>(zenon_Hf
zenon_He)))) (fun zenon_Hd=>(zenon_or _ _ (fun zenon_Hb=>(zenon_Hc
zenon_Hb)) (fun zenon_Ha=>(zenon_or _ _ (fun zenon_H8=>(zenon_H9
zenon_H8)) (fun zenon_H7=>(zenon_or _ _ (fun zenon_H5=>(zenon_H6
zenon_H5)) (fun zenon_H4=>(zenon_H4 zenon_H3)) zenon_H7)) zenon_Ha))
zenon_Hd)) __D_1_2_LEMMA)) (fun zenon_Hd=>(zenon_or _ _ (fun zenon_Hb=>(
zenon_Hc zenon_Hb)) (fun zenon_Ha=>(zenon_or _ _ (fun zenon_H8=>(
zenon_H9 zenon_H8)) (fun zenon_H7=>(zenon_or _ _ (fun zenon_H5=>(
zenon_H6 zenon_H5)) (fun zenon_H4=>(zenon_H4 zenon_H3)) zenon_H7))
zenon_Ha)) zenon_Hd)) __D_1_1_LEMMA)))) zenon_H12)) zenon_H13)) zenon_G)
))).
Qed.

      Theorem __D_1_LEMMA :
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter va vb vc)) va))) \/
           Is_true ((((basics._equal_ _) (abst_value (abst_voter va vb vc))
                       vb))) \/
             Is_true ((((basics._equal_ _) (abst_value (abst_voter va vb vc))
                         vc))) \/
               (~Is_true (((_p_P_valid (abst_diag (abst_voter va vb vc))))))).
      apply for_zenon___D_1_LEMMA;
      auto.
      Qed.
      End __D_1.
(* File "vote.fcl", line 266, characters 2-15 *)
Theorem for_zenon_voter_returns_an_input_value:(forall va:_p_V_T,(
forall vb:_p_V_T,(forall vc:_p_V_T,((Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) va))\/((Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vb))\/((Is_true (basics._equal_ _ (
abst_value (abst_voter va vb vc)) vc))\/(~(Is_true (_p_P_valid (
abst_diag (abst_voter va vb vc))))))))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G __D_1_LEMMA)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_voter_returns_an_input_value :
      forall v1  v2  v3 : _p_V_T,
        Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v1))) \/
          Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                      v2))) \/
            Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                        v3))) \/
              (~Is_true (((_p_P_valid (abst_diag (abst_voter v1 v2 v3)))))).
    assert (__force_use_p_E_T := _p_E_T).
    assert (__force_use_p_C_T := _p_C_T).
    assert (__force_use_p_V_T := _p_V_T).
    assert (__force_use_p_P_T := _p_P_T).
    assert (__force_use__p_E_equal := _p_E_equal).
    assert (__force_use__p_E_no_match := _p_E_no_match).
    assert (__force_use__p_E_partial_match := _p_E_partial_match).
    assert (__force_use__p_E_perfect_match := _p_E_perfect_match).
    assert (__force_use__p_E_range_match := _p_E_range_match).
    assert (__force_use__p_C_capt_1 := _p_C_capt_1).
    assert (__force_use__p_C_capt_2 := _p_C_capt_2).
    assert (__force_use__p_C_capt_3 := _p_C_capt_3).
    assert (__force_use__p_V_consistency_rule := _p_V_consistency_rule).
    assert (__force_use__p_P_constr := _p_P_constr).
    assert (__force_use__p_P_prj_b := _p_P_prj_b).
    assert (__force_use__p_P_valid := _p_P_valid).
    assert (__force_use__p_P_prj_b_is_snd_of_pair :=
      _p_P_prj_b_is_snd_of_pair).
    assert (__force_use__p_P_no_match_is_invalid :=
      _p_P_no_match_is_invalid).
    assert (__force_use_abst_diag := abst_diag).
    assert (__force_use_abst_state := abst_state).
    assert (__force_use_abst_value := abst_value).
    assert (__force_use_abst_voter := abst_voter).
    assert (__force_use_abst_vote_match_c1 := abst_vote_match_c1).
    assert (__force_use_abst_vote_match_c2 := abst_vote_match_c2).
    assert (__force_use_abst_vote_match_c3 := abst_vote_match_c3).
    assert (__force_use_abst_vote_no_match := abst_vote_no_match).
    assert (__force_use_abst_vote_partial_c1 := abst_vote_partial_c1).
    assert (__force_use_abst_vote_partial_c2 := abst_vote_partial_c2).
    assert (__force_use_abst_vote_partial_c3 := abst_vote_partial_c3).
    assert (__force_use_abst_vote_perfect := abst_vote_perfect).
    apply for_zenon_voter_returns_an_input_value;
    auto.
    Qed.
    End Proof_of_voter_returns_an_input_value.
  
  Theorem voter_returns_an_input_value  (_p_E_T : Set) (_p_C_T : Set)
    (_p_V_T : Set) (_p_P_T : Set) (_p_E_equal :
    _p_E_T -> _p_E_T -> basics.bool__t) (_p_E_no_match : _p_E_T)
    (_p_E_partial_match : _p_E_T) (_p_E_perfect_match : _p_E_T)
    (_p_E_range_match : _p_E_T) (_p_C_capt_1 : _p_C_T) (_p_C_capt_2 : _p_C_T)
    (_p_C_capt_3 : _p_C_T) (_p_V_consistency_rule :
    _p_V_T -> _p_V_T -> basics.bool__t) (_p_P_constr :
    _p_C_T -> _p_E_T -> _p_P_T) (_p_P_prj_b : _p_P_T -> _p_E_T) (_p_P_valid :
    _p_P_T -> basics.bool__t) (_p_P_prj_b_is_snd_of_pair :
    forall n1 : _p_C_T,
      forall n2 : _p_E_T,
        Is_true ((_p_E_equal (_p_P_prj_b (_p_P_constr n1 n2)) n2)))
    (_p_P_no_match_is_invalid :
    forall x : _p_P_T,
      Is_true ((_p_E_equal (_p_P_prj_b x) _p_E_no_match)) ->
        ~Is_true (((_p_P_valid x))))
    (abst_diag : (Datatypes.prod _p_V_T _p_P_T) -> _p_P_T) (abst_state :=
    state _p_E_T _p_P_T _p_P_prj_b)
    (abst_value : (Datatypes.prod _p_V_T _p_P_T) -> _p_V_T)
    (abst_voter : _p_V_T ->
                    _p_V_T -> _p_V_T -> (Datatypes.prod _p_V_T _p_P_T))
    (abst_vote_match_c1 :
    forall v1  v2  v3 : _p_V_T,
      (~Is_true ((_p_V_consistency_rule v1 v2)) /\
         ~Is_true ((_p_V_consistency_rule v1 v3)) /\
           Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v2))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_1 _p_E_range_match))))))
    (abst_vote_match_c2 :
    forall v1  v2  v3 : _p_V_T,
      (~Is_true ((_p_V_consistency_rule v1 v2)) /\
         Is_true ((_p_V_consistency_rule v1 v3)) /\
           ~Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v3))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_2 _p_E_range_match))))))
    (abst_vote_match_c3 :
    forall v1  v2  v3 : _p_V_T,
      (Is_true ((_p_V_consistency_rule v1 v2)) /\
         ~Is_true ((_p_V_consistency_rule v1 v3)) /\
           ~Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v1))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_3 _p_E_range_match))))))
    (abst_vote_no_match :
    forall v1  v2  v3 : _p_V_T,
      (~Is_true ((_p_V_consistency_rule v1 v2)) /\
         ~Is_true ((_p_V_consistency_rule v1 v3)) /\
           ~Is_true ((_p_V_consistency_rule v2 v3))) ->
        Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                    (_p_P_constr _p_C_capt_1 _p_E_no_match)))))
    (abst_vote_partial_c1 :
    forall v1  v2  v3 : _p_V_T,
      (Is_true ((_p_V_consistency_rule v1 v2)) /\
         Is_true ((_p_V_consistency_rule v1 v3)) /\
           ~Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v1))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_1 _p_E_partial_match))))))
    (abst_vote_partial_c2 :
    forall v1  v2  v3 : _p_V_T,
      (Is_true ((_p_V_consistency_rule v1 v2)) /\
         ~Is_true ((_p_V_consistency_rule v1 v3)) /\
           Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v2))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_2 _p_E_partial_match))))))
    (abst_vote_partial_c3 :
    forall v1  v2  v3 : _p_V_T,
      (~Is_true ((_p_V_consistency_rule v1 v2)) /\
         Is_true ((_p_V_consistency_rule v1 v3)) /\
           Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v3))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_3 _p_E_partial_match))))))
    (abst_vote_perfect :
    forall v1  v2  v3 : _p_V_T,
      (Is_true ((_p_V_consistency_rule v1 v2)) /\
         Is_true ((_p_V_consistency_rule v2 v3)) /\
           Is_true ((_p_V_consistency_rule v1 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v1))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_1 _p_E_perfect_match)))))):
    forall v1  v2  v3 : _p_V_T,
      Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v1))) \/
        Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v2))) \/
          Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                      v3))) \/
            (~Is_true (((_p_P_valid (abst_diag (abst_voter v1 v2 v3)))))).
  apply for_zenon_abstracted_voter_returns_an_input_value;
  auto.
  Qed.
  
End Voteur.

Module Imp_vote.
  Definition voter (_p_E_T : Set) (_p_C_T : Set) (_p_V_T : Set) (_p_P_T :
    Set) (_p_E_no_match : _p_E_T) (_p_E_partial_match : _p_E_T)
    (_p_E_perfect_match : _p_E_T) (_p_E_range_match : _p_E_T) (_p_C_capt_1 :
    _p_C_T) (_p_C_capt_2 : _p_C_T) (_p_C_capt_3 : _p_C_T)
    (_p_V_consistency_rule : _p_V_T -> _p_V_T -> basics.bool__t)
    (_p_P_constr : _p_C_T -> _p_E_T -> _p_P_T) (v1 : _p_V_T) (v2 : _p_V_T)
    (v3 : _p_V_T) : (Datatypes.prod _p_V_T _p_P_T) :=
    let c1 : basics.bool__t :=
      (_p_V_consistency_rule v1 v2)
    in
    let c2 : basics.bool__t :=
      (_p_V_consistency_rule v1 v3)
    in
    let c3 : basics.bool__t :=
      (_p_V_consistency_rule v2 v3)
    in
    (if c1
      then (if c2
             then (if c3
                    then (v1, (_p_P_constr _p_C_capt_1 _p_E_perfect_match))
                    else (v1, (_p_P_constr _p_C_capt_1 _p_E_partial_match)))
             else (if c3
                    then (v2, (_p_P_constr _p_C_capt_2 _p_E_partial_match))
                    else (v1, (_p_P_constr _p_C_capt_3 _p_E_range_match))))
      else (if c2
             then (if c3
                    then (v3, (_p_P_constr _p_C_capt_3 _p_E_partial_match))
                    else (v3, (_p_P_constr _p_C_capt_2 _p_E_range_match)))
             else (if c3
                    then (v2, (_p_P_constr _p_C_capt_1 _p_E_range_match))
                    else (v1, (_p_P_constr _p_C_capt_1 _p_E_no_match))))).
  
  (* From species vote#Imp_vote. *)
  Theorem vote_match_c1  (_p_E_T : Set) (_p_C_T : Set) (_p_V_T : Set)
    (_p_P_T : Set) (_p_E_range_match : _p_E_T) (_p_C_capt_1 : _p_C_T)
    (_p_V_consistency_rule : _p_V_T -> _p_V_T -> basics.bool__t)
    (_p_P_constr : _p_C_T -> _p_E_T -> _p_P_T)
    (abst_diag : (Datatypes.prod _p_V_T _p_P_T) -> _p_P_T)
    (abst_value : (Datatypes.prod _p_V_T _p_P_T) -> _p_V_T)
    (abst_voter : _p_V_T ->
                    _p_V_T -> _p_V_T -> (Datatypes.prod _p_V_T _p_P_T)):
    forall v1  v2  v3 : _p_V_T,
      (~Is_true ((_p_V_consistency_rule v1 v2)) /\
         ~Is_true ((_p_V_consistency_rule v1 v3)) /\
           Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v2))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_1 _p_E_range_match))))).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
  (* From species vote#Imp_vote. *)
  Theorem vote_match_c2  (_p_E_T : Set) (_p_C_T : Set) (_p_V_T : Set)
    (_p_P_T : Set) (_p_E_range_match : _p_E_T) (_p_C_capt_2 : _p_C_T)
    (_p_V_consistency_rule : _p_V_T -> _p_V_T -> basics.bool__t)
    (_p_P_constr : _p_C_T -> _p_E_T -> _p_P_T)
    (abst_diag : (Datatypes.prod _p_V_T _p_P_T) -> _p_P_T)
    (abst_value : (Datatypes.prod _p_V_T _p_P_T) -> _p_V_T)
    (abst_voter : _p_V_T ->
                    _p_V_T -> _p_V_T -> (Datatypes.prod _p_V_T _p_P_T)):
    forall v1  v2  v3 : _p_V_T,
      (~Is_true ((_p_V_consistency_rule v1 v2)) /\
         Is_true ((_p_V_consistency_rule v1 v3)) /\
           ~Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v3))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_2 _p_E_range_match))))).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
  (* From species vote#Imp_vote. *)
  Theorem vote_match_c3  (_p_E_T : Set) (_p_C_T : Set) (_p_V_T : Set)
    (_p_P_T : Set) (_p_E_range_match : _p_E_T) (_p_C_capt_3 : _p_C_T)
    (_p_V_consistency_rule : _p_V_T -> _p_V_T -> basics.bool__t)
    (_p_P_constr : _p_C_T -> _p_E_T -> _p_P_T)
    (abst_diag : (Datatypes.prod _p_V_T _p_P_T) -> _p_P_T)
    (abst_value : (Datatypes.prod _p_V_T _p_P_T) -> _p_V_T)
    (abst_voter : _p_V_T ->
                    _p_V_T -> _p_V_T -> (Datatypes.prod _p_V_T _p_P_T)):
    forall v1  v2  v3 : _p_V_T,
      (Is_true ((_p_V_consistency_rule v1 v2)) /\
         ~Is_true ((_p_V_consistency_rule v1 v3)) /\
           ~Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v1))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_3 _p_E_range_match))))).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
  (* From species vote#Imp_vote. *)
  Theorem vote_no_match  (_p_E_T : Set) (_p_C_T : Set) (_p_V_T : Set)
    (_p_P_T : Set) (_p_E_no_match : _p_E_T) (_p_C_capt_1 : _p_C_T)
    (_p_V_consistency_rule : _p_V_T -> _p_V_T -> basics.bool__t)
    (_p_P_constr : _p_C_T -> _p_E_T -> _p_P_T)
    (abst_diag : (Datatypes.prod _p_V_T _p_P_T) -> _p_P_T)
    (abst_voter : _p_V_T ->
                    _p_V_T -> _p_V_T -> (Datatypes.prod _p_V_T _p_P_T)):
    forall v1  v2  v3 : _p_V_T,
      (~Is_true ((_p_V_consistency_rule v1 v2)) /\
         ~Is_true ((_p_V_consistency_rule v1 v3)) /\
           ~Is_true ((_p_V_consistency_rule v2 v3))) ->
        Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                    (_p_P_constr _p_C_capt_1 _p_E_no_match)))).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
  (* From species vote#Imp_vote. *)
  Theorem vote_partial_c1  (_p_E_T : Set) (_p_C_T : Set) (_p_V_T : Set)
    (_p_P_T : Set) (_p_E_partial_match : _p_E_T) (_p_C_capt_1 : _p_C_T)
    (_p_V_consistency_rule : _p_V_T -> _p_V_T -> basics.bool__t)
    (_p_P_constr : _p_C_T -> _p_E_T -> _p_P_T)
    (abst_diag : (Datatypes.prod _p_V_T _p_P_T) -> _p_P_T)
    (abst_value : (Datatypes.prod _p_V_T _p_P_T) -> _p_V_T)
    (abst_voter : _p_V_T ->
                    _p_V_T -> _p_V_T -> (Datatypes.prod _p_V_T _p_P_T)):
    forall v1  v2  v3 : _p_V_T,
      (Is_true ((_p_V_consistency_rule v1 v2)) /\
         Is_true ((_p_V_consistency_rule v1 v3)) /\
           ~Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v1))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_1 _p_E_partial_match))))).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
  (* From species vote#Imp_vote. *)
  Theorem vote_partial_c2  (_p_E_T : Set) (_p_C_T : Set) (_p_V_T : Set)
    (_p_P_T : Set) (_p_E_partial_match : _p_E_T) (_p_C_capt_2 : _p_C_T)
    (_p_V_consistency_rule : _p_V_T -> _p_V_T -> basics.bool__t)
    (_p_P_constr : _p_C_T -> _p_E_T -> _p_P_T)
    (abst_diag : (Datatypes.prod _p_V_T _p_P_T) -> _p_P_T)
    (abst_value : (Datatypes.prod _p_V_T _p_P_T) -> _p_V_T)
    (abst_voter : _p_V_T ->
                    _p_V_T -> _p_V_T -> (Datatypes.prod _p_V_T _p_P_T)):
    forall v1  v2  v3 : _p_V_T,
      (Is_true ((_p_V_consistency_rule v1 v2)) /\
         ~Is_true ((_p_V_consistency_rule v1 v3)) /\
           Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v2))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_2 _p_E_partial_match))))).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
  (* From species vote#Imp_vote. *)
  Theorem vote_partial_c3  (_p_E_T : Set) (_p_C_T : Set) (_p_V_T : Set)
    (_p_P_T : Set) (_p_E_partial_match : _p_E_T) (_p_C_capt_3 : _p_C_T)
    (_p_V_consistency_rule : _p_V_T -> _p_V_T -> basics.bool__t)
    (_p_P_constr : _p_C_T -> _p_E_T -> _p_P_T)
    (abst_diag : (Datatypes.prod _p_V_T _p_P_T) -> _p_P_T)
    (abst_value : (Datatypes.prod _p_V_T _p_P_T) -> _p_V_T)
    (abst_voter : _p_V_T ->
                    _p_V_T -> _p_V_T -> (Datatypes.prod _p_V_T _p_P_T)):
    forall v1  v2  v3 : _p_V_T,
      (~Is_true ((_p_V_consistency_rule v1 v2)) /\
         Is_true ((_p_V_consistency_rule v1 v3)) /\
           Is_true ((_p_V_consistency_rule v2 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v3))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_3 _p_E_partial_match))))).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
  (* From species vote#Imp_vote. *)
  Theorem vote_perfect  (_p_E_T : Set) (_p_C_T : Set) (_p_V_T : Set)
    (_p_P_T : Set) (_p_E_perfect_match : _p_E_T) (_p_C_capt_1 : _p_C_T)
    (_p_V_consistency_rule : _p_V_T -> _p_V_T -> basics.bool__t)
    (_p_P_constr : _p_C_T -> _p_E_T -> _p_P_T)
    (abst_diag : (Datatypes.prod _p_V_T _p_P_T) -> _p_P_T)
    (abst_value : (Datatypes.prod _p_V_T _p_P_T) -> _p_V_T)
    (abst_voter : _p_V_T ->
                    _p_V_T -> _p_V_T -> (Datatypes.prod _p_V_T _p_P_T)):
    forall v1  v2  v3 : _p_V_T,
      (Is_true ((_p_V_consistency_rule v1 v2)) /\
         Is_true ((_p_V_consistency_rule v2 v3)) /\
           Is_true ((_p_V_consistency_rule v1 v3))) ->
        (Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v1))) /\
           Is_true ((((basics._equal_ _) (abst_diag (abst_voter v1 v2 v3))
                       (_p_P_constr _p_C_capt_1 _p_E_perfect_match))))).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
  (* From species vote#Imp_vote. *)
  Theorem voter_returns_an_input_value  (_p_E_T : Set) (_p_C_T : Set)
    (_p_V_T : Set) (_p_P_T : Set) (_p_P_valid : _p_P_T -> basics.bool__t)
    (abst_diag : (Datatypes.prod _p_V_T _p_P_T) -> _p_P_T)
    (abst_value : (Datatypes.prod _p_V_T _p_P_T) -> _p_V_T)
    (abst_voter : _p_V_T ->
                    _p_V_T -> _p_V_T -> (Datatypes.prod _p_V_T _p_P_T)):
    forall v1  v2  v3 : _p_V_T,
      Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v1))) \/
        Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3)) v2))) \/
          Is_true ((((basics._equal_ _) (abst_value (abst_voter v1 v2 v3))
                      v3))) \/
            (~Is_true (((_p_P_valid (abst_diag (abst_voter v1 v2 v3)))))).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
End Imp_vote.

