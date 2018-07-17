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
Require gen_diag.
Require etat_vote.
Require num_capteur.
Require pair.
Module Diag_2oo3.
  
End Diag_2oo3.

Module Imp_diag_2oo3.
  Record me_as_species (E_T : Set) (C_T : Set) (_p_E_equal : E_T ->
                                                               E_T ->
                                                                 basics.bool__t)
    (_p_E_no_match : E_T) (_p_E_partial_match : E_T)
    (_p_E_perfect_match : E_T) (_p_E_range_match : E_T)
    (_p_C_equal : C_T -> C_T -> basics.bool__t) : Type :=
    mk_record {
    rf_T : Set ;
    (* From species pair#Imp_pair. *)
    rf_constr : C_T -> E_T -> rf_T ;
    (* From species pair#Imp_pair. *)
    rf_equal : rf_T -> rf_T -> basics.bool__t ;
    (* From species basics#Basic_object. *)
    rf_parse : basics.string__t -> rf_T ;
    (* From species basics#Basic_object. *)
    rf_print : rf_T -> basics.string__t ;
    (* From species pair#Imp_pair. *)
    rf_prj_a : rf_T -> C_T ;
    (* From species pair#Imp_pair. *)
    rf_prj_b : rf_T -> E_T ;
    (* From species pair#Imp_pair. *)
    rf_element : rf_T ;
    (* From species sets#Setoid. *)
    rf_different : rf_T -> rf_T -> basics.bool__t ;
    (* From species pair#Imp_pair. *)
    rf_prj_a_is_first_of_pair :
      forall n1 : C_T,
        forall n2 : E_T,
          Is_true ((_p_C_equal (rf_prj_a (rf_constr n1 n2)) n1)) ;
    (* From species pair#Imp_pair. *)
    rf_def_equal :
      forall p1  p2 : rf_T,
        Is_true ((rf_equal p1 p2)) <->
          (Is_true ((_p_C_equal (rf_prj_a p1) (rf_prj_a p2))) /\
             Is_true ((_p_E_equal (rf_prj_b p1) (rf_prj_b p2)))) ;
    (* From species pair#Imp_pair. *)
    rf_prj_b_is_snd_of_pair :
      forall n1 : C_T,
        forall n2 : E_T,
          Is_true ((_p_E_equal (rf_prj_b (rf_constr n1 n2)) n2)) ;
    (* From species pair#Imp_pair. *)
    rf_unicite_1 :
      forall a : rf_T,
        Is_true ((rf_equal (rf_constr (rf_prj_a a) (rf_prj_b a)) a)) ;
    (* From species pair#Imp_pair. *)
    rf_unicite_2 :
      forall a : rf_T,
        Is_true ((rf_equal a (rf_constr (rf_prj_a a) (rf_prj_b a)))) ;
    (* From species diag#Imp_diag_2oo3. *)
    rf_valid : rf_T -> basics.bool__t ;
    (* From species sets#Setoid. *)
    rf_same_is_not_different :
      forall x  y : rf_T,
        Is_true ((rf_different x y)) <-> ~Is_true (((rf_equal x y))) ;
    (* From species pair#Imp_pair. *)
    rf_equal_transitive :
      forall x  y  z : rf_T,
        Is_true ((rf_equal x y)) ->
          Is_true ((rf_equal y z)) -> Is_true ((rf_equal x z)) ;
    (* From species pair#Imp_pair. *)
    rf_def_equal1 :
      forall n1  n3 : C_T,
        forall n2  n4 : E_T,
          Is_true ((rf_equal (rf_constr n1 n2) (rf_constr n3 n4))) <->
            (Is_true ((_p_C_equal n1 n3)) /\ Is_true ((_p_E_equal n2 n4))) ;
    (* From species diag#Imp_diag_2oo3. *)
    rf_no_match_is_invalid :
      forall x : rf_T,
        Is_true ((_p_E_equal (rf_prj_b x) _p_E_no_match)) ->
          ~Is_true (((rf_valid x))) ;
    (* From species diag#Imp_diag_2oo3. *)
    rf_partial_match_is_valid :
      forall x : rf_T,
        Is_true ((_p_E_equal (rf_prj_b x) _p_E_partial_match)) ->
          Is_true ((rf_valid x)) ;
    (* From species diag#Imp_diag_2oo3. *)
    rf_perfect_match_is_valid :
      forall x : rf_T,
        Is_true ((_p_E_equal (rf_prj_b x) _p_E_perfect_match)) ->
          Is_true ((rf_valid x)) ;
    (* From species diag#Imp_diag_2oo3. *)
    rf_range_match_is_valid :
      forall x : rf_T,
        Is_true ((_p_E_equal (rf_prj_b x) _p_E_range_match)) ->
          Is_true ((rf_valid x)) ;
    (* From species pair#Imp_pair. *)
    rf_equal_reflexive : forall x : rf_T, Is_true ((rf_equal x x)) ;
    (* From species pair#Imp_pair. *)
    rf_equal_reflexive2 :
      forall n1 : C_T,
        forall n2 : E_T,
          Is_true ((rf_equal (rf_constr n1 n2) (rf_constr n1 n2))) ;
    (* From species pair#Imp_pair. *)
    rf_equal_symmetric2 :
      forall n1  n3 : C_T,
        forall n2  n4 : E_T,
          Is_true ((rf_equal (rf_constr n1 n2) (rf_constr n3 n4))) ->
            Is_true ((rf_equal (rf_constr n3 n4) (rf_constr n1 n2))) ;
    (* From species pair#Imp_pair. *)
    rf_equal_transitive2 :
      forall n1  n3  n5 : C_T,
        forall n2  n4  n6 : E_T,
          Is_true ((rf_equal (rf_constr n1 n2) (rf_constr n3 n4))) ->
            Is_true ((rf_equal (rf_constr n3 n4) (rf_constr n5 n6))) ->
              Is_true ((rf_equal (rf_constr n1 n2) (rf_constr n5 n6))) ;
    (* From species sets#Setoid. *)
    rf_different_is_irreflexive :
      forall x : rf_T, ~Is_true (((rf_different x x))) ;
    (* From species pair#Imp_pair. *)
    rf_equal_symmetric :
      forall x  y : rf_T,
        Is_true ((rf_equal x y)) -> Is_true ((rf_equal y x)) ;
    (* From species sets#Setoid. *)
    rf_different_is_complete :
      forall x  y  z : rf_T,
        Is_true ((rf_different x y)) ->
          (Is_true ((rf_different x z)) \/ Is_true ((rf_different y z))) ;
    (* From species sets#Setoid. *)
    rf_different_is_symmetric :
      forall x  y : rf_T,
        Is_true ((rf_different x y)) -> Is_true ((rf_different y x))
    }.
  
  Definition valid (_p_E_T : Set) (_p_C_T : Set) (_p_E_equal :
    _p_E_T -> _p_E_T -> basics.bool__t) (_p_E_partial_match : _p_E_T)
    (_p_E_perfect_match : _p_E_T) (_p_E_range_match : _p_E_T) (abst_T : Set)
    (abst_prj_b : abst_T -> _p_E_T) (x : abst_T) : basics.bool__t :=
    (basics._bar__bar_ (_p_E_equal (abst_prj_b x) _p_E_range_match)
      (basics._bar__bar_ (_p_E_equal (abst_prj_b x) _p_E_partial_match)
        (_p_E_equal (abst_prj_b x) _p_E_perfect_match))).
  
  (* From species diag#Imp_diag_2oo3. *)
  (* Section for proof of theorem 'no_match_is_invalid'. *)
  Section Proof_of_no_match_is_invalid.
    Variable _p_E_T : Set.
    Variable _p_C_T : Set.
    Variable _p_E_equal : _p_E_T -> _p_E_T -> basics.bool__t.
    Variable _p_E_no_match : _p_E_T.
    Variable _p_E_partial_match : _p_E_T.
    Variable _p_E_perfect_match : _p_E_T.
    Variable _p_E_range_match : _p_E_T.
    Variable _p_E_all_field_different_0_1 :
      ~Is_true (((_p_E_equal _p_E_no_match _p_E_range_match))).
    Variable _p_E_all_field_different_0_2 :
      ~Is_true (((_p_E_equal _p_E_no_match _p_E_partial_match))).
    Variable _p_E_all_field_different_0_3 :
      ~Is_true (((_p_E_equal _p_E_no_match _p_E_perfect_match))).
    Variable _p_E_equal_symmetric :
      forall x  y : _p_E_T,
        Is_true ((_p_E_equal x y)) -> Is_true ((_p_E_equal y x)).
    Variable _p_E_equal_transitive :
      forall x  y  z : _p_E_T,
        Is_true ((_p_E_equal x y)) ->
          Is_true ((_p_E_equal y z)) -> Is_true ((_p_E_equal x z)).
    Variable abst_T : Set.
    Variable abst_prj_b : abst_T -> _p_E_T.
    Let abst_valid := valid _p_E_T _p_C_T _p_E_equal _p_E_partial_match
    _p_E_perfect_match _p_E_range_match abst_T
    abst_prj_b.
    Section __A_1.
      Variable x : abst_T.
      Variable H1 : Is_true ((_p_E_equal (abst_prj_b x) _p_E_no_match)).
(* File "diag.fcl", line 77, character 4, line 81, character 26 *)
Theorem for_zenon___A_1_LEMMA:(~(Is_true (abst_valid x))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G (fun zenon_H35=>(let zenon_H34
:=zenon_H35 in (let zenon_H33:=zenon_H34 in (zenon_focal_or (_p_E_equal
(abst_prj_b x) _p_E_range_match) (basics._bar__bar_ (_p_E_equal (
abst_prj_b x) _p_E_partial_match) (_p_E_equal (abst_prj_b x)
_p_E_perfect_match)) (fun zenon_H32=>(zenon_or _ _ (fun zenon_H2b=>(let
zenon_H19:=(fun zenon_H1e=>(zenon_and _ _ (fun zenon_H17 zenon_He=>(
zenon_all _p_E_T (fun x:_p_E_T=>(forall y:_p_E_T,((Is_true (_p_E_equal
x y))->(Is_true (_p_E_equal y x))))) (abst_prj_b x) (fun zenon_H1d=>(
zenon_all _p_E_T (fun y:_p_E_T=>((Is_true (_p_E_equal (abst_prj_b x) y))
->(Is_true (_p_E_equal y (abst_prj_b x))))) _p_E_no_match (fun
zenon_H1c=>(zenon_imply _ _ (fun zenon_H1b=>(zenon_H1b H1)) (fun
zenon_Hd=>(zenon_He zenon_Hd)) zenon_H1c)) zenon_H1d))
_p_E_equal_symmetric)) zenon_H1e)) in (let zenon_H2a:=(fun zenon_H31=>(
zenon_subst _ (fun zenon_Vl=>(Is_true zenon_Vl)) (_p_E_equal (
abst_prj_b x) _p_E_range_match) (_p_E_equal _p_E_no_match
_p_E_range_match) (fun zenon_H2c=>(zenon_subst _ (fun zenon_Vm=>(~((
_p_E_equal zenon_Vm _p_E_range_match) = (_p_E_equal _p_E_no_match
_p_E_range_match)))) (abst_prj_b x) _p_E_no_match (fun zenon_H14=>(
zenon_notand _ _ (fun zenon_H18=>(zenon_H18 (fun zenon_H16=>(let
zenon_H13:=(fun zenon_H15=>(zenon_subst _ (fun zenon_Vn=>(zenon_Vn =
_p_E_no_match)) _p_E_no_match (abst_prj_b x) (fun zenon_H17=>(zenon_H17
zenon_H16)) zenon_H14 zenon_H15)) in (zenon_noteq _ _p_E_no_match
zenon_H13))))) (fun zenon_H12=>(zenon_H12 (fun zenon_Hd=>(zenon_all
_p_E_T (fun x:_p_E_T=>(forall y:_p_E_T,(forall z:_p_E_T,((Is_true (
_p_E_equal x y))->((Is_true (_p_E_equal y z))->(Is_true (_p_E_equal x z)
)))))) _p_E_no_match (fun zenon_H11=>(zenon_all _p_E_T (fun y:_p_E_T=>(
forall z:_p_E_T,((Is_true (_p_E_equal _p_E_no_match y))->((Is_true (
_p_E_equal y z))->(Is_true (_p_E_equal _p_E_no_match z)))))) (
abst_prj_b x) (fun zenon_H10=>(zenon_all _p_E_T (fun z:_p_E_T=>((
Is_true (_p_E_equal _p_E_no_match (abst_prj_b x)))->((Is_true (
_p_E_equal (abst_prj_b x) z))->(Is_true (_p_E_equal _p_E_no_match z)))))
 _p_E_range_match (fun zenon_H30=>(zenon_imply _ _ (fun zenon_He=>(
zenon_He zenon_Hd)) (fun zenon_H2f=>(zenon_imply _ _ (fun zenon_H2e=>(
zenon_H2e zenon_H2b)) (fun zenon_H2d=>(_p_E_all_field_different_0_1
zenon_H2d)) zenon_H2f)) zenon_H30)) zenon_H10)) zenon_H11))
_p_E_equal_transitive)))) zenon_H19)) (zenon_notnot _ (refl_equal (
_p_E_equal _p_E_no_match _p_E_range_match))) zenon_H2c))
_p_E_all_field_different_0_1 zenon_H2b)) in (zenon_noteq _
_p_E_range_match zenon_H2a)))) (fun zenon_H29=>(let zenon_H28
:=zenon_H29 in (zenon_focal_or (_p_E_equal (abst_prj_b x)
_p_E_partial_match) (_p_E_equal (abst_prj_b x) _p_E_perfect_match) (fun
zenon_H27=>(zenon_or _ _ (fun zenon_H20=>(let zenon_H19:=(fun
zenon_H1e=>(zenon_and _ _ (fun zenon_H17 zenon_He=>(zenon_all _p_E_T (
fun x:_p_E_T=>(forall y:_p_E_T,((Is_true (_p_E_equal x y))->(Is_true (
_p_E_equal y x))))) (abst_prj_b x) (fun zenon_H1d=>(zenon_all _p_E_T (
fun y:_p_E_T=>((Is_true (_p_E_equal (abst_prj_b x) y))->(Is_true (
_p_E_equal y (abst_prj_b x))))) _p_E_no_match (fun zenon_H1c=>(
zenon_imply _ _ (fun zenon_H1b=>(zenon_H1b H1)) (fun zenon_Hd=>(
zenon_He zenon_Hd)) zenon_H1c)) zenon_H1d)) _p_E_equal_symmetric))
zenon_H1e)) in (let zenon_H1f:=(fun zenon_H26=>(zenon_subst _ (fun
zenon_Vi=>(Is_true zenon_Vi)) (_p_E_equal (abst_prj_b x)
_p_E_partial_match) (_p_E_equal _p_E_no_match _p_E_partial_match) (fun
zenon_H21=>(zenon_subst _ (fun zenon_Vj=>(~((_p_E_equal zenon_Vj
_p_E_partial_match) = (_p_E_equal _p_E_no_match _p_E_partial_match)))) (
abst_prj_b x) _p_E_no_match (fun zenon_H14=>(zenon_notand _ _ (fun
zenon_H18=>(zenon_H18 (fun zenon_H16=>(let zenon_H13:=(fun zenon_H15=>(
zenon_subst _ (fun zenon_Vk=>(zenon_Vk = _p_E_no_match)) _p_E_no_match (
abst_prj_b x) (fun zenon_H17=>(zenon_H17 zenon_H16)) zenon_H14
zenon_H15)) in (zenon_noteq _ _p_E_no_match zenon_H13))))) (fun
zenon_H12=>(zenon_H12 (fun zenon_Hd=>(zenon_all _p_E_T (fun x:_p_E_T=>(
forall y:_p_E_T,(forall z:_p_E_T,((Is_true (_p_E_equal x y))->((Is_true
(_p_E_equal y z))->(Is_true (_p_E_equal x z))))))) _p_E_no_match (fun
zenon_H11=>(zenon_all _p_E_T (fun y:_p_E_T=>(forall z:_p_E_T,((Is_true (
_p_E_equal _p_E_no_match y))->((Is_true (_p_E_equal y z))->(Is_true (
_p_E_equal _p_E_no_match z)))))) (abst_prj_b x) (fun zenon_H10=>(
zenon_all _p_E_T (fun z:_p_E_T=>((Is_true (_p_E_equal _p_E_no_match (
abst_prj_b x)))->((Is_true (_p_E_equal (abst_prj_b x) z))->(Is_true (
_p_E_equal _p_E_no_match z))))) _p_E_partial_match (fun zenon_H25=>(
zenon_imply _ _ (fun zenon_He=>(zenon_He zenon_Hd)) (fun zenon_H24=>(
zenon_imply _ _ (fun zenon_H23=>(zenon_H23 zenon_H20)) (fun zenon_H22=>(
_p_E_all_field_different_0_2 zenon_H22)) zenon_H24)) zenon_H25))
zenon_H10)) zenon_H11)) _p_E_equal_transitive)))) zenon_H19)) (
zenon_notnot _ (refl_equal (_p_E_equal _p_E_no_match _p_E_partial_match)
)) zenon_H21)) _p_E_all_field_different_0_2 zenon_H20)) in (zenon_noteq
_ _p_E_partial_match zenon_H1f)))) (fun zenon_H8=>(let zenon_H19:=(fun
zenon_H1e=>(zenon_and _ _ (fun zenon_H17 zenon_He=>(zenon_all _p_E_T (
fun x:_p_E_T=>(forall y:_p_E_T,((Is_true (_p_E_equal x y))->(Is_true (
_p_E_equal y x))))) (abst_prj_b x) (fun zenon_H1d=>(zenon_all _p_E_T (
fun y:_p_E_T=>((Is_true (_p_E_equal (abst_prj_b x) y))->(Is_true (
_p_E_equal y (abst_prj_b x))))) _p_E_no_match (fun zenon_H1c=>(
zenon_imply _ _ (fun zenon_H1b=>(zenon_H1b H1)) (fun zenon_Hd=>(
zenon_He zenon_Hd)) zenon_H1c)) zenon_H1d)) _p_E_equal_symmetric))
zenon_H1e)) in (let zenon_H7:=(fun zenon_H1a=>(zenon_subst _ (fun
zenon_Vf=>(Is_true zenon_Vf)) (_p_E_equal (abst_prj_b x)
_p_E_perfect_match) (_p_E_equal _p_E_no_match _p_E_perfect_match) (fun
zenon_H9=>(zenon_subst _ (fun zenon_Vg=>(~((_p_E_equal zenon_Vg
_p_E_perfect_match) = (_p_E_equal _p_E_no_match _p_E_perfect_match)))) (
abst_prj_b x) _p_E_no_match (fun zenon_H14=>(zenon_notand _ _ (fun
zenon_H18=>(zenon_H18 (fun zenon_H16=>(let zenon_H13:=(fun zenon_H15=>(
zenon_subst _ (fun zenon_Vh=>(zenon_Vh = _p_E_no_match)) _p_E_no_match (
abst_prj_b x) (fun zenon_H17=>(zenon_H17 zenon_H16)) zenon_H14
zenon_H15)) in (zenon_noteq _ _p_E_no_match zenon_H13))))) (fun
zenon_H12=>(zenon_H12 (fun zenon_Hd=>(zenon_all _p_E_T (fun x:_p_E_T=>(
forall y:_p_E_T,(forall z:_p_E_T,((Is_true (_p_E_equal x y))->((Is_true
(_p_E_equal y z))->(Is_true (_p_E_equal x z))))))) _p_E_no_match (fun
zenon_H11=>(zenon_all _p_E_T (fun y:_p_E_T=>(forall z:_p_E_T,((Is_true (
_p_E_equal _p_E_no_match y))->((Is_true (_p_E_equal y z))->(Is_true (
_p_E_equal _p_E_no_match z)))))) (abst_prj_b x) (fun zenon_H10=>(
zenon_all _p_E_T (fun z:_p_E_T=>((Is_true (_p_E_equal _p_E_no_match (
abst_prj_b x)))->((Is_true (_p_E_equal (abst_prj_b x) z))->(Is_true (
_p_E_equal _p_E_no_match z))))) _p_E_perfect_match (fun zenon_Hf=>(
zenon_imply _ _ (fun zenon_He=>(zenon_He zenon_Hd)) (fun zenon_Hc=>(
zenon_imply _ _ (fun zenon_Hb=>(zenon_Hb zenon_H8)) (fun zenon_Ha=>(
_p_E_all_field_different_0_3 zenon_Ha)) zenon_Hc)) zenon_Hf)) zenon_H10)
) zenon_H11)) _p_E_equal_transitive)))) zenon_H19)) (zenon_notnot _ (
refl_equal (_p_E_equal _p_E_no_match _p_E_perfect_match))) zenon_H9))
_p_E_all_field_different_0_3 zenon_H8)) in (zenon_noteq _
_p_E_perfect_match zenon_H7)))) zenon_H27)) zenon_H28))) zenon_H32))
zenon_H33)))))))).
Qed.

      Theorem __A_1_LEMMA : ~Is_true (((abst_valid x))).
      assert (__force_use_H1 := H1).
      apply for_zenon___A_1_LEMMA;
      auto.
      Qed.
      End __A_1.
(* File "diag.fcl", line 82, characters 11-38 *)
Theorem for_zenon_no_match_is_invalid:(forall x:abst_T,((Is_true (
_p_E_equal (abst_prj_b x) _p_E_no_match))->(~(Is_true (abst_valid x)))))
.
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G __A_1_LEMMA)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_no_match_is_invalid :
      forall x : abst_T,
        Is_true ((_p_E_equal (abst_prj_b x) _p_E_no_match)) ->
          ~Is_true (((abst_valid x))).
    assert (__force_use_p_E_T := _p_E_T).
    assert (__force_use_p_C_T := _p_C_T).
    assert (__force_use__p_E_equal := _p_E_equal).
    assert (__force_use__p_E_no_match := _p_E_no_match).
    assert (__force_use__p_E_partial_match := _p_E_partial_match).
    assert (__force_use__p_E_perfect_match := _p_E_perfect_match).
    assert (__force_use__p_E_range_match := _p_E_range_match).
    assert (__force_use__p_E_all_field_different_0_1 :=
      _p_E_all_field_different_0_1).
    assert (__force_use__p_E_all_field_different_0_2 :=
      _p_E_all_field_different_0_2).
    assert (__force_use__p_E_all_field_different_0_3 :=
      _p_E_all_field_different_0_3).
    assert (__force_use__p_E_equal_symmetric := _p_E_equal_symmetric).
    assert (__force_use__p_E_equal_transitive := _p_E_equal_transitive).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_prj_b := abst_prj_b).
    assert (__force_use_abst_valid := abst_valid).
    apply for_zenon_no_match_is_invalid;
    auto.
    Qed.
    End Proof_of_no_match_is_invalid.
  
  Theorem no_match_is_invalid  (_p_E_T : Set) (_p_C_T : Set) (_p_E_equal :
    _p_E_T -> _p_E_T -> basics.bool__t) (_p_E_no_match : _p_E_T)
    (_p_E_partial_match : _p_E_T) (_p_E_perfect_match : _p_E_T)
    (_p_E_range_match : _p_E_T) (_p_E_all_field_different_0_1 :
    ~Is_true (((_p_E_equal _p_E_no_match _p_E_range_match))))
    (_p_E_all_field_different_0_2 :
    ~Is_true (((_p_E_equal _p_E_no_match _p_E_partial_match))))
    (_p_E_all_field_different_0_3 :
    ~Is_true (((_p_E_equal _p_E_no_match _p_E_perfect_match))))
    (_p_E_equal_symmetric :
    forall x  y : _p_E_T,
      Is_true ((_p_E_equal x y)) -> Is_true ((_p_E_equal y x)))
    (_p_E_equal_transitive :
    forall x  y  z : _p_E_T,
      Is_true ((_p_E_equal x y)) ->
        Is_true ((_p_E_equal y z)) -> Is_true ((_p_E_equal x z)))
    (abst_T : Set) (abst_prj_b : abst_T -> _p_E_T) (abst_valid := valid
    _p_E_T _p_C_T _p_E_equal _p_E_partial_match _p_E_perfect_match
    _p_E_range_match abst_T abst_prj_b):
    forall x : abst_T,
      Is_true ((_p_E_equal (abst_prj_b x) _p_E_no_match)) ->
        ~Is_true (((abst_valid x))).
  apply for_zenon_abstracted_no_match_is_invalid;
  auto.
  Qed.
  
  (* From species diag#Imp_diag_2oo3. *)
  (* Section for proof of theorem 'partial_match_is_valid'. *)
  Section Proof_of_partial_match_is_valid.
    Variable _p_E_T : Set.
    Variable _p_C_T : Set.
    Variable _p_E_equal : _p_E_T -> _p_E_T -> basics.bool__t.
    Variable _p_E_partial_match : _p_E_T.
    Variable _p_E_perfect_match : _p_E_T.
    Variable _p_E_range_match : _p_E_T.
    Variable abst_T : Set.
    Variable abst_prj_b : abst_T -> _p_E_T.
    Let abst_valid := valid _p_E_T _p_C_T _p_E_equal _p_E_partial_match
    _p_E_perfect_match _p_E_range_match abst_T
    abst_prj_b.
(* File "diag.fcl", line 88, characters 2-24 *)
Theorem for_zenon_partial_match_is_valid:(forall x:abst_T,((Is_true (
_p_E_equal (abst_prj_b x) _p_E_partial_match))->(Is_true (abst_valid x))
)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>((Is_true (
_p_E_equal (abst_prj_b x) _p_E_partial_match))->(Is_true (abst_valid x))
)) (fun zenon_He=>(zenon_ex abst_T (fun x:abst_T=>(~((Is_true (
_p_E_equal (abst_prj_b x) _p_E_partial_match))->(Is_true (abst_valid x))
))) (fun(zenon_Tx_b:abst_T) zenon_Hd=>(zenon_notimply _ _ (fun zenon_H2
zenon_Hc=>(let zenon_Hb:=zenon_Hc in (let zenon_Ha:=zenon_Hb in (
zenon_focal_notor (_p_E_equal (abst_prj_b zenon_Tx_b) _p_E_range_match)
(basics._bar__bar_ (_p_E_equal (abst_prj_b zenon_Tx_b)
_p_E_partial_match) (_p_E_equal (abst_prj_b zenon_Tx_b)
_p_E_perfect_match)) (fun zenon_H9=>(zenon_notor _ _ (fun zenon_H8
zenon_H7=>(let zenon_H6:=zenon_H7 in (zenon_focal_notor (_p_E_equal (
abst_prj_b zenon_Tx_b) _p_E_partial_match) (_p_E_equal (abst_prj_b
zenon_Tx_b) _p_E_perfect_match) (fun zenon_H5=>(zenon_notor _ _ (fun
zenon_H3 zenon_H4=>(zenon_H3 zenon_H2)) zenon_H5)) zenon_H6))) zenon_H9)
) zenon_Ha)))) zenon_Hd)) zenon_He)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_partial_match_is_valid :
      forall x : abst_T,
        Is_true ((_p_E_equal (abst_prj_b x) _p_E_partial_match)) ->
          Is_true ((abst_valid x)).
    assert (__force_use_p_E_T := _p_E_T).
    assert (__force_use_p_C_T := _p_C_T).
    assert (__force_use__p_E_equal := _p_E_equal).
    assert (__force_use__p_E_partial_match := _p_E_partial_match).
    assert (__force_use__p_E_perfect_match := _p_E_perfect_match).
    assert (__force_use__p_E_range_match := _p_E_range_match).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_prj_b := abst_prj_b).
    assert (__force_use_abst_valid := abst_valid).
    apply for_zenon_partial_match_is_valid;
    auto.
    Qed.
    End Proof_of_partial_match_is_valid.
  
  Theorem partial_match_is_valid  (_p_E_T : Set) (_p_C_T : Set) (_p_E_equal :
    _p_E_T -> _p_E_T -> basics.bool__t) (_p_E_partial_match : _p_E_T)
    (_p_E_perfect_match : _p_E_T) (_p_E_range_match : _p_E_T) (abst_T : Set)
    (abst_prj_b : abst_T -> _p_E_T) (abst_valid := valid _p_E_T _p_C_T
    _p_E_equal _p_E_partial_match _p_E_perfect_match _p_E_range_match abst_T
    abst_prj_b):
    forall x : abst_T,
      Is_true ((_p_E_equal (abst_prj_b x) _p_E_partial_match)) ->
        Is_true ((abst_valid x)).
  apply for_zenon_abstracted_partial_match_is_valid;
  auto.
  Qed.
  
  (* From species diag#Imp_diag_2oo3. *)
  (* Section for proof of theorem 'perfect_match_is_valid'. *)
  Section Proof_of_perfect_match_is_valid.
    Variable _p_E_T : Set.
    Variable _p_C_T : Set.
    Variable _p_E_equal : _p_E_T -> _p_E_T -> basics.bool__t.
    Variable _p_E_partial_match : _p_E_T.
    Variable _p_E_perfect_match : _p_E_T.
    Variable _p_E_range_match : _p_E_T.
    Variable abst_T : Set.
    Variable abst_prj_b : abst_T -> _p_E_T.
    Let abst_valid := valid _p_E_T _p_C_T _p_E_equal _p_E_partial_match
    _p_E_perfect_match _p_E_range_match abst_T
    abst_prj_b.
(* File "diag.fcl", line 91, characters 2-24 *)
Theorem for_zenon_perfect_match_is_valid:(forall x:abst_T,((Is_true (
_p_E_equal (abst_prj_b x) _p_E_perfect_match))->(Is_true (abst_valid x))
)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>((Is_true (
_p_E_equal (abst_prj_b x) _p_E_perfect_match))->(Is_true (abst_valid x))
)) (fun zenon_He=>(zenon_ex abst_T (fun x:abst_T=>(~((Is_true (
_p_E_equal (abst_prj_b x) _p_E_perfect_match))->(Is_true (abst_valid x))
))) (fun(zenon_Tx_b:abst_T) zenon_Hd=>(zenon_notimply _ _ (fun zenon_H2
zenon_Hc=>(let zenon_Hb:=zenon_Hc in (let zenon_Ha:=zenon_Hb in (
zenon_focal_notor (_p_E_equal (abst_prj_b zenon_Tx_b) _p_E_range_match)
(basics._bar__bar_ (_p_E_equal (abst_prj_b zenon_Tx_b)
_p_E_partial_match) (_p_E_equal (abst_prj_b zenon_Tx_b)
_p_E_perfect_match)) (fun zenon_H9=>(zenon_notor _ _ (fun zenon_H8
zenon_H7=>(let zenon_H6:=zenon_H7 in (zenon_focal_notor (_p_E_equal (
abst_prj_b zenon_Tx_b) _p_E_partial_match) (_p_E_equal (abst_prj_b
zenon_Tx_b) _p_E_perfect_match) (fun zenon_H5=>(zenon_notor _ _ (fun
zenon_H4 zenon_H3=>(zenon_H3 zenon_H2)) zenon_H5)) zenon_H6))) zenon_H9)
) zenon_Ha)))) zenon_Hd)) zenon_He)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_perfect_match_is_valid :
      forall x : abst_T,
        Is_true ((_p_E_equal (abst_prj_b x) _p_E_perfect_match)) ->
          Is_true ((abst_valid x)).
    assert (__force_use_p_E_T := _p_E_T).
    assert (__force_use_p_C_T := _p_C_T).
    assert (__force_use__p_E_equal := _p_E_equal).
    assert (__force_use__p_E_partial_match := _p_E_partial_match).
    assert (__force_use__p_E_perfect_match := _p_E_perfect_match).
    assert (__force_use__p_E_range_match := _p_E_range_match).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_prj_b := abst_prj_b).
    assert (__force_use_abst_valid := abst_valid).
    apply for_zenon_perfect_match_is_valid;
    auto.
    Qed.
    End Proof_of_perfect_match_is_valid.
  
  Theorem perfect_match_is_valid  (_p_E_T : Set) (_p_C_T : Set) (_p_E_equal :
    _p_E_T -> _p_E_T -> basics.bool__t) (_p_E_partial_match : _p_E_T)
    (_p_E_perfect_match : _p_E_T) (_p_E_range_match : _p_E_T) (abst_T : Set)
    (abst_prj_b : abst_T -> _p_E_T) (abst_valid := valid _p_E_T _p_C_T
    _p_E_equal _p_E_partial_match _p_E_perfect_match _p_E_range_match abst_T
    abst_prj_b):
    forall x : abst_T,
      Is_true ((_p_E_equal (abst_prj_b x) _p_E_perfect_match)) ->
        Is_true ((abst_valid x)).
  apply for_zenon_abstracted_perfect_match_is_valid;
  auto.
  Qed.
  
  (* From species diag#Imp_diag_2oo3. *)
  (* Section for proof of theorem 'range_match_is_valid'. *)
  Section Proof_of_range_match_is_valid.
    Variable _p_E_T : Set.
    Variable _p_C_T : Set.
    Variable _p_E_equal : _p_E_T -> _p_E_T -> basics.bool__t.
    Variable _p_E_partial_match : _p_E_T.
    Variable _p_E_perfect_match : _p_E_T.
    Variable _p_E_range_match : _p_E_T.
    Variable abst_T : Set.
    Variable abst_prj_b : abst_T -> _p_E_T.
    Let abst_valid := valid _p_E_T _p_C_T _p_E_equal _p_E_partial_match
    _p_E_perfect_match _p_E_range_match abst_T
    abst_prj_b.
(* File "diag.fcl", line 85, characters 2-24 *)
Theorem for_zenon_range_match_is_valid:(forall x:abst_T,((Is_true (
_p_E_equal (abst_prj_b x) _p_E_range_match))->(Is_true (abst_valid x))))
.
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>((Is_true (
_p_E_equal (abst_prj_b x) _p_E_range_match))->(Is_true (abst_valid x))))
 (fun zenon_Ha=>(zenon_ex abst_T (fun x:abst_T=>(~((Is_true (_p_E_equal
(abst_prj_b x) _p_E_range_match))->(Is_true (abst_valid x))))) (fun(
zenon_Tx_b:abst_T) zenon_H9=>(zenon_notimply _ _ (fun zenon_H2
zenon_H8=>(let zenon_H7:=zenon_H8 in (let zenon_H6:=zenon_H7 in (
zenon_focal_notor (_p_E_equal (abst_prj_b zenon_Tx_b) _p_E_range_match)
(basics._bar__bar_ (_p_E_equal (abst_prj_b zenon_Tx_b)
_p_E_partial_match) (_p_E_equal (abst_prj_b zenon_Tx_b)
_p_E_perfect_match)) (fun zenon_H5=>(zenon_notor _ _ (fun zenon_H3
zenon_H4=>(zenon_H3 zenon_H2)) zenon_H5)) zenon_H6)))) zenon_H9))
zenon_Ha)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_range_match_is_valid :
      forall x : abst_T,
        Is_true ((_p_E_equal (abst_prj_b x) _p_E_range_match)) ->
          Is_true ((abst_valid x)).
    assert (__force_use_p_E_T := _p_E_T).
    assert (__force_use_p_C_T := _p_C_T).
    assert (__force_use__p_E_equal := _p_E_equal).
    assert (__force_use__p_E_partial_match := _p_E_partial_match).
    assert (__force_use__p_E_perfect_match := _p_E_perfect_match).
    assert (__force_use__p_E_range_match := _p_E_range_match).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_prj_b := abst_prj_b).
    assert (__force_use_abst_valid := abst_valid).
    apply for_zenon_range_match_is_valid;
    auto.
    Qed.
    End Proof_of_range_match_is_valid.
  
  Theorem range_match_is_valid  (_p_E_T : Set) (_p_C_T : Set) (_p_E_equal :
    _p_E_T -> _p_E_T -> basics.bool__t) (_p_E_partial_match : _p_E_T)
    (_p_E_perfect_match : _p_E_T) (_p_E_range_match : _p_E_T) (abst_T : Set)
    (abst_prj_b : abst_T -> _p_E_T) (abst_valid := valid _p_E_T _p_C_T
    _p_E_equal _p_E_partial_match _p_E_perfect_match _p_E_range_match abst_T
    abst_prj_b):
    forall x : abst_T,
      Is_true ((_p_E_equal (abst_prj_b x) _p_E_range_match)) ->
        Is_true ((abst_valid x)).
  apply for_zenon_abstracted_range_match_is_valid;
  auto.
  Qed.
  
  (* Fully defined 'Imp_diag_2oo3' species's collection generator. *)
  Definition collection_create (_p_E_T : Set) (_p_C_T : Set) _p_E_element
    _p_E_equal _p_E_no_match _p_E_partial_match _p_E_perfect_match
    _p_E_range_match _p_E_all_field_different_0_1
    _p_E_all_field_different_0_2 _p_E_all_field_different_0_3
    _p_E_equal_reflexive _p_E_equal_symmetric _p_E_equal_transitive
    _p_C_element _p_C_equal _p_C_equal_reflexive _p_C_equal_symmetric
    _p_C_equal_transitive :=
    let local_rep := (Datatypes.prod _p_C_T _p_E_T) in
    (* From species pair#Imp_pair. *)
    let local_constr := pair.Imp_pair.constr _p_C_T _p_E_T in
    (* From species pair#Imp_pair. *)
    let local_equal := pair.Imp_pair.equal _p_C_T _p_E_T _p_C_equal
      _p_E_equal in
    (* From species basics#Basic_object. *)
    let local_parse := basics.Basic_object.parse local_rep in
    (* From species basics#Basic_object. *)
    let local_print := basics.Basic_object.print local_rep in
    (* From species pair#Imp_pair. *)
    let local_prj_a := pair.Imp_pair.prj_a _p_C_T _p_E_T in
    (* From species pair#Imp_pair. *)
    let local_prj_b := pair.Imp_pair.prj_b _p_C_T _p_E_T in
    (* From species pair#Imp_pair. *)
    let local_element := pair.Imp_pair.element _p_C_T _p_E_T _p_C_element
      _p_E_element local_rep local_constr in
    (* From species sets#Setoid. *)
    let local_different := sets.Setoid.different local_rep local_equal in
    (* From species pair#Imp_pair. *)
    let local_prj_a_is_first_of_pair := pair.Imp_pair.prj_a_is_first_of_pair
      _p_C_T _p_E_T _p_C_equal local_rep local_constr local_prj_a in
    (* From species pair#Imp_pair. *)
    let local_def_equal := pair.Imp_pair.def_equal _p_C_T _p_E_T _p_C_equal
      _p_E_equal local_rep local_equal local_prj_a local_prj_b in
    (* From species pair#Imp_pair. *)
    let local_prj_b_is_snd_of_pair := pair.Imp_pair.prj_b_is_snd_of_pair
      _p_C_T _p_E_T _p_E_equal local_rep local_constr local_prj_b in
    (* From species pair#Imp_pair. *)
    let local_unicite_1 := pair.Imp_pair.unicite_1 _p_C_T _p_E_T local_rep
      local_constr local_equal local_prj_a local_prj_b in
    (* From species pair#Imp_pair. *)
    let local_unicite_2 := pair.Imp_pair.unicite_2 _p_C_T _p_E_T local_rep
      local_constr local_equal local_prj_a local_prj_b in
    (* From species diag#Imp_diag_2oo3. *)
    let local_valid := valid _p_E_T _p_C_T _p_E_equal _p_E_partial_match
      _p_E_perfect_match _p_E_range_match local_rep local_prj_b in
    (* From species sets#Setoid. *)
    let local_same_is_not_different := sets.Setoid.same_is_not_different
      local_rep local_equal in
    (* From species pair#Imp_pair. *)
    let local_equal_transitive := pair.Imp_pair.equal_transitive _p_C_T
      _p_E_T _p_C_equal _p_C_equal_transitive _p_E_equal
      _p_E_equal_transitive local_rep local_equal local_prj_a local_prj_b
      local_def_equal in
    (* From species pair#Imp_pair. *)
    let local_def_equal1 := pair.Imp_pair.def_equal1 _p_C_T _p_E_T _p_C_equal
      _p_C_equal_symmetric _p_C_equal_transitive _p_E_equal
      _p_E_equal_symmetric _p_E_equal_transitive local_rep local_constr
      local_equal local_prj_a local_prj_b local_prj_a_is_first_of_pair
      local_def_equal local_prj_b_is_snd_of_pair in
    (* From species diag#Imp_diag_2oo3. *)
    let local_no_match_is_invalid := no_match_is_invalid _p_E_T _p_C_T
      _p_E_equal _p_E_no_match _p_E_partial_match _p_E_perfect_match
      _p_E_range_match _p_E_all_field_different_0_1
      _p_E_all_field_different_0_2 _p_E_all_field_different_0_3
      _p_E_equal_symmetric _p_E_equal_transitive local_rep local_prj_b in
    (* From species diag#Imp_diag_2oo3. *)
    let local_partial_match_is_valid := partial_match_is_valid _p_E_T _p_C_T
      _p_E_equal _p_E_partial_match _p_E_perfect_match _p_E_range_match
      local_rep local_prj_b in
    (* From species diag#Imp_diag_2oo3. *)
    let local_perfect_match_is_valid := perfect_match_is_valid _p_E_T _p_C_T
      _p_E_equal _p_E_partial_match _p_E_perfect_match _p_E_range_match
      local_rep local_prj_b in
    (* From species diag#Imp_diag_2oo3. *)
    let local_range_match_is_valid := range_match_is_valid _p_E_T _p_C_T
      _p_E_equal _p_E_partial_match _p_E_perfect_match _p_E_range_match
      local_rep local_prj_b in
    (* From species pair#Imp_pair. *)
    let local_equal_reflexive := pair.Imp_pair.equal_reflexive _p_C_T _p_E_T
      local_rep local_constr local_equal local_prj_a local_prj_b
      local_unicite_1 local_unicite_2 local_equal_transitive in
    (* From species pair#Imp_pair. *)
    let local_equal_reflexive2 := pair.Imp_pair.equal_reflexive2 _p_C_T
      _p_E_T _p_C_equal _p_C_equal_reflexive _p_E_equal _p_E_equal_reflexive
      local_rep local_constr local_equal local_def_equal1 in
    (* From species pair#Imp_pair. *)
    let local_equal_symmetric2 := pair.Imp_pair.equal_symmetric2 _p_C_T
      _p_E_T _p_C_equal _p_C_equal_symmetric _p_E_equal _p_E_equal_symmetric
      local_rep local_constr local_equal local_def_equal1 in
    (* From species pair#Imp_pair. *)
    let local_equal_transitive2 := pair.Imp_pair.equal_transitive2 _p_C_T
      _p_E_T _p_C_equal _p_C_equal_transitive _p_E_equal
      _p_E_equal_transitive local_rep local_constr local_equal
      local_def_equal1 in
    (* From species sets#Setoid. *)
    let local_different_is_irreflexive :=
      sets.Setoid.different_is_irreflexive local_rep local_equal
      local_different local_equal_reflexive local_same_is_not_different in
    (* From species pair#Imp_pair. *)
    let local_equal_symmetric := pair.Imp_pair.equal_symmetric _p_C_T _p_E_T
      local_rep local_constr local_equal local_prj_a local_prj_b
      local_unicite_1 local_unicite_2 local_equal_transitive
      local_equal_symmetric2 in
    (* From species sets#Setoid. *)
    let local_different_is_complete := sets.Setoid.different_is_complete
      local_rep local_equal local_different local_equal_reflexive
      local_equal_symmetric local_equal_transitive
      local_same_is_not_different in
    (* From species sets#Setoid. *)
    let local_different_is_symmetric := sets.Setoid.different_is_symmetric
      local_rep local_equal local_different local_equal_symmetric
      local_same_is_not_different in
    mk_record (_p_E_T : Set) (_p_C_T : Set) _p_E_equal _p_E_no_match
    _p_E_partial_match _p_E_perfect_match _p_E_range_match _p_C_equal
    local_rep local_constr local_equal local_parse local_print local_prj_a
    local_prj_b local_element local_different local_prj_a_is_first_of_pair
    local_def_equal local_prj_b_is_snd_of_pair local_unicite_1
    local_unicite_2 local_valid local_same_is_not_different
    local_equal_transitive local_def_equal1 local_no_match_is_invalid
    local_partial_match_is_valid local_perfect_match_is_valid
    local_range_match_is_valid local_equal_reflexive local_equal_reflexive2
    local_equal_symmetric2 local_equal_transitive2
    local_different_is_irreflexive local_equal_symmetric
    local_different_is_complete local_different_is_symmetric.
  
End Imp_diag_2oo3.

