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
Require peano.
Module Sp_capteur.
  
End Sp_capteur.

Module Imp_capteur.
  Record me_as_species (P_T : Set) : Type :=
    mk_record {
    rf_T : Set ;
    (* From species num_capteur#Imp_capteur. *)
    rf_capt_1 : rf_T ;
    (* From species num_capteur#Imp_capteur. *)
    rf_equal : rf_T -> rf_T -> basics.bool__t ;
    (* From species basics#Basic_object. *)
    rf_parse : basics.string__t -> rf_T ;
    (* From species num_capteur#Imp_capteur. *)
    rf_capt_2 : rf_T ;
    (* From species num_capteur#Imp_capteur. *)
    rf_element : rf_T ;
    (* From species sets#Setoid. *)
    rf_different : rf_T -> rf_T -> basics.bool__t ;
    (* From species num_capteur#Imp_capteur. *)
    rf_equal_reflexive : forall x : rf_T, Is_true ((rf_equal x x)) ;
    (* From species num_capteur#Imp_capteur. *)
    rf_equal_symmetric :
      forall x  y : rf_T,
        Is_true ((rf_equal x y)) -> Is_true ((rf_equal y x)) ;
    (* From species num_capteur#Imp_capteur. *)
    rf_equal_transitive :
      forall x  y  z : rf_T,
        Is_true ((rf_equal x y)) ->
          Is_true ((rf_equal y z)) -> Is_true ((rf_equal x z)) ;
    (* From species num_capteur#Imp_capteur. *)
    rf_all_field_different_0_1 :
      ~Is_true (((rf_equal rf_capt_1 rf_capt_2))) ;
    (* From species num_capteur#Imp_capteur. *)
    rf_capt_3 : rf_T ;
    (* From species sets#Setoid. *)
    rf_same_is_not_different :
      forall x  y : rf_T,
        Is_true ((rf_different x y)) <-> ~Is_true (((rf_equal x y))) ;
    (* From species num_capteur#Imp_capteur. *)
    rf_all_field_different_0_2 :
      ~Is_true (((rf_equal rf_capt_1 rf_capt_3))) ;
    (* From species num_capteur#Imp_capteur. *)
    rf_all_field_different_1_2 :
      ~Is_true (((rf_equal rf_capt_2 rf_capt_3))) ;
    (* From species num_capteur#Imp_capteur. *)
    rf_all_value :
      forall e : rf_T,
        Is_true ((rf_equal e rf_capt_1)) \/
          Is_true ((rf_equal e rf_capt_2)) \/
            Is_true ((rf_equal e rf_capt_3)) ;
    (* From species num_capteur#Imp_capteur. *)
    rf_print : rf_T -> basics.string__t ;
    (* From species sets#Setoid. *)
    rf_different_is_complete :
      forall x  y  z : rf_T,
        Is_true ((rf_different x y)) ->
          (Is_true ((rf_different x z)) \/ Is_true ((rf_different y z))) ;
    (* From species sets#Setoid. *)
    rf_different_is_irreflexive :
      forall x : rf_T, ~Is_true (((rf_different x x))) ;
    (* From species sets#Setoid. *)
    rf_different_is_symmetric :
      forall x  y : rf_T,
        Is_true ((rf_different x y)) -> Is_true ((rf_different y x))
    }.
  
  Definition capt_1 (_p_P_T : Set) (_p_P_zero : _p_P_T) (abst_T := _p_P_T) :
    abst_T := _p_P_zero.
  Definition equal (_p_P_T : Set) (_p_P_equal :
    _p_P_T -> _p_P_T -> basics.bool__t) (abst_T := _p_P_T) (x : abst_T)
    (y : abst_T) : basics.bool__t := (_p_P_equal x y).
  Definition capt_2 (_p_P_T : Set) (_p_P_s : _p_P_T -> _p_P_T)
    (abst_T := _p_P_T) (abst_capt_1 : abst_T) : abst_T :=
    (_p_P_s abst_capt_1).
  Definition element (_p_P_T : Set) (abst_T : Set) (abst_capt_1 : abst_T) :
    abst_T := abst_capt_1.
  
  (* From species num_capteur#Imp_capteur. *)
  (* Section for proof of theorem 'equal_reflexive'. *)
  Section Proof_of_equal_reflexive.
    Variable _p_P_T : Set.
    Variable _p_P_equal : _p_P_T -> _p_P_T -> basics.bool__t.
    Variable _p_P_equal_reflexive :
      forall x : _p_P_T, Is_true ((_p_P_equal x x)).
    Let abst_T := _p_P_T.
    Let abst_equal := equal _p_P_T
    _p_P_equal.
(* File "num_capteur.fcl", line 74, characters 4-53 *)
Theorem for_zenon_equal_reflexive:(forall x:abst_T,(Is_true (abst_equal
x x))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>(Is_true (
abst_equal x x))) (fun zenon_H6=>(zenon_ex abst_T (fun x:abst_T=>(~(
Is_true (abst_equal x x)))) (fun(zenon_Tx_e:abst_T) zenon_H5=>(let
zenon_H3:=zenon_H5 in (zenon_all _p_P_T (fun x:_p_P_T=>(Is_true (
_p_P_equal x x))) zenon_Tx_e (fun zenon_H2=>(zenon_H3 zenon_H2))
_p_P_equal_reflexive))) zenon_H6)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_reflexive :
      forall x : abst_T, Is_true ((abst_equal x x)).
    assert (__force_use_p_P_T := _p_P_T).
    assert (__force_use__p_P_equal := _p_P_equal).
    assert (__force_use__p_P_equal_reflexive := _p_P_equal_reflexive).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_equal := abst_equal).
    apply for_zenon_equal_reflexive;
    auto.
    Qed.
    End Proof_of_equal_reflexive.
  
  Theorem equal_reflexive  (_p_P_T : Set) (_p_P_equal :
    _p_P_T -> _p_P_T -> basics.bool__t) (_p_P_equal_reflexive :
    forall x : _p_P_T, Is_true ((_p_P_equal x x))) (abst_T := _p_P_T)
    (abst_equal := equal _p_P_T _p_P_equal):
    forall x : abst_T, Is_true ((abst_equal x x)).
  apply for_zenon_abstracted_equal_reflexive;
  auto.
  Qed.
  
  (* From species num_capteur#Imp_capteur. *)
  (* Section for proof of theorem 'equal_symmetric'. *)
  Section Proof_of_equal_symmetric.
    Variable _p_P_T : Set.
    Variable _p_P_equal : _p_P_T -> _p_P_T -> basics.bool__t.
    Variable _p_P_equal_symmetric :
      forall x  y : _p_P_T,
        Is_true ((_p_P_equal x y)) -> Is_true ((_p_P_equal y x)).
    Let abst_T := _p_P_T.
    Let abst_equal := equal _p_P_T
    _p_P_equal.
(* File "num_capteur.fcl", line 72, characters 4-53 *)
Theorem for_zenon_equal_symmetric:(forall x:abst_T,(forall y:abst_T,((
Is_true (abst_equal x y))->(Is_true (abst_equal y x))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>(forall y:abst_T,((
Is_true (abst_equal x y))->(Is_true (abst_equal y x))))) (fun zenon_Hf=>
(zenon_ex abst_T (fun x:abst_T=>(~(forall y:abst_T,((Is_true (
abst_equal x y))->(Is_true (abst_equal y x)))))) (fun(zenon_Tx_c:abst_T)
 zenon_He=>(zenon_notallex (fun y:abst_T=>((Is_true (abst_equal
zenon_Tx_c y))->(Is_true (abst_equal y zenon_Tx_c)))) (fun zenon_Hd=>(
zenon_ex abst_T (fun y:abst_T=>(~((Is_true (abst_equal zenon_Tx_c y))->(
Is_true (abst_equal y zenon_Tx_c))))) (fun(zenon_Ty_j:abst_T) zenon_Hc=>
(zenon_notimply _ _ (fun zenon_Hb zenon_Ha=>(let zenon_H5:=zenon_Hb in (
let zenon_H4:=zenon_Ha in (zenon_all _p_P_T (fun x:_p_P_T=>(forall y
:_p_P_T,((Is_true (_p_P_equal x y))->(Is_true (_p_P_equal y x)))))
zenon_Tx_c (fun zenon_H8=>(zenon_all _p_P_T (fun y:_p_P_T=>((Is_true (
_p_P_equal zenon_Tx_c y))->(Is_true (_p_P_equal y zenon_Tx_c))))
zenon_Ty_j (fun zenon_H7=>(zenon_imply _ _ (fun zenon_H6=>(zenon_H6
zenon_H5)) (fun zenon_H3=>(zenon_H4 zenon_H3)) zenon_H7)) zenon_H8))
_p_P_equal_symmetric)))) zenon_Hc)) zenon_Hd)) zenon_He)) zenon_Hf))
zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_symmetric :
      forall x  y : abst_T,
        Is_true ((abst_equal x y)) -> Is_true ((abst_equal y x)).
    assert (__force_use_p_P_T := _p_P_T).
    assert (__force_use__p_P_equal := _p_P_equal).
    assert (__force_use__p_P_equal_symmetric := _p_P_equal_symmetric).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_equal := abst_equal).
    apply for_zenon_equal_symmetric;
    auto.
    Qed.
    End Proof_of_equal_symmetric.
  
  Theorem equal_symmetric  (_p_P_T : Set) (_p_P_equal :
    _p_P_T -> _p_P_T -> basics.bool__t) (_p_P_equal_symmetric :
    forall x  y : _p_P_T,
      Is_true ((_p_P_equal x y)) -> Is_true ((_p_P_equal y x)))
    (abst_T := _p_P_T) (abst_equal := equal _p_P_T _p_P_equal):
    forall x  y : abst_T,
      Is_true ((abst_equal x y)) -> Is_true ((abst_equal y x)).
  apply for_zenon_abstracted_equal_symmetric;
  auto.
  Qed.
  
  (* From species num_capteur#Imp_capteur. *)
  (* Section for proof of theorem 'equal_transitive'. *)
  Section Proof_of_equal_transitive.
    Variable _p_P_T : Set.
    Variable _p_P_equal : _p_P_T -> _p_P_T -> basics.bool__t.
    Variable _p_P_equal_transitive :
      forall x  y  z : _p_P_T,
        (Is_true ((_p_P_equal x y)) /\ Is_true ((_p_P_equal y z))) ->
          Is_true ((_p_P_equal x z)).
    Let abst_T := _p_P_T.
    Let abst_equal := equal _p_P_T
    _p_P_equal.
(* File "num_capteur.fcl", line 70, characters 4-54 *)
Theorem for_zenon_equal_transitive:(forall x:abst_T,(forall y:abst_T,(
forall z:abst_T,((Is_true (abst_equal x y))->((Is_true (abst_equal y z))
->(Is_true (abst_equal x z))))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(let zenon_H13:=(fun zenon_H23=>(zenon_notallex (
fun x:abst_T=>(forall y:abst_T,(forall z:abst_T,((Is_true (abst_equal x
y))->((Is_true (abst_equal y z))->(Is_true (abst_equal x z))))))) (fun
zenon_H37=>(zenon_ex abst_T (fun x:abst_T=>(~(forall y:abst_T,(forall z
:abst_T,((Is_true (abst_equal x y))->((Is_true (abst_equal y z))->(
Is_true (abst_equal x z)))))))) (fun(zenon_Tx_u:abst_T) zenon_H36=>(
zenon_notallex (fun y:abst_T=>(forall z:abst_T,((Is_true (abst_equal
zenon_Tx_u y))->((Is_true (abst_equal y z))->(Is_true (abst_equal
zenon_Tx_u z)))))) (fun zenon_H35=>(zenon_ex abst_T (fun y:abst_T=>(~(
forall z:abst_T,((Is_true (abst_equal zenon_Tx_u y))->((Is_true (
abst_equal y z))->(Is_true (abst_equal zenon_Tx_u z))))))) (fun(
zenon_Ty_v:abst_T) zenon_H34=>(zenon_notallex (fun z:abst_T=>((Is_true (
abst_equal zenon_Tx_u zenon_Ty_v))->((Is_true (abst_equal zenon_Ty_v z))
->(Is_true (abst_equal zenon_Tx_u z))))) (fun zenon_H33=>(zenon_ex
abst_T (fun z:abst_T=>(~((Is_true (abst_equal zenon_Tx_u zenon_Ty_v))->(
(Is_true (abst_equal zenon_Ty_v z))->(Is_true (abst_equal zenon_Tx_u z))
)))) (fun(zenon_Tz_x:abst_T) zenon_H32=>(zenon_notimply _ _ (fun
zenon_H30 zenon_H31=>(zenon_notimply _ _ (fun zenon_H2f zenon_H2e=>(let
zenon_H1e:=zenon_H30 in (let zenon_H19:=zenon_H2f in (let zenon_H18
:=zenon_H2e in (let zenon_H2b:=(fun zenon_H2d=>(zenon_and _ _ (fun
zenon_H29 zenon_H1f=>(zenon_H1f zenon_H1e)) zenon_H2d)) in (let
zenon_H16:=(fun zenon_H2c=>(zenon_subst _ (fun zenon_Vf=>(Is_true
zenon_Vf)) (_p_P_equal zenon_Ty_v zenon_Tz_x) (_p_P_equal zenon_Tx_u
zenon_Tz_x) (fun zenon_H1a=>(zenon_subst _ (fun zenon_Vg=>(~((
_p_P_equal zenon_Vg zenon_Tz_x) = (_p_P_equal zenon_Tx_u zenon_Tz_x))))
zenon_Ty_v zenon_Tx_u (fun zenon_H26=>(zenon_notand _ _ (fun zenon_H2a=>
(zenon_H2a (fun zenon_H28=>(let zenon_H25:=(fun zenon_H27=>(zenon_subst
_ (fun zenon_Vh=>(zenon_Vh = zenon_Tx_u)) zenon_Tx_u zenon_Ty_v (fun
zenon_H29=>(zenon_H29 zenon_H28)) zenon_H26 zenon_H27)) in (zenon_noteq
_ zenon_Tx_u zenon_H25))))) (fun zenon_H24=>(zenon_H24 (fun zenon_H1e=>(
zenon_all _p_P_T (fun x:_p_P_T=>(forall y:_p_P_T,(forall z:_p_P_T,((
Is_true (_p_P_equal x y))->((Is_true (_p_P_equal y z))->(Is_true (
_p_P_equal x z))))))) zenon_Tx_u (fun zenon_H22=>(zenon_all _p_P_T (fun
y:_p_P_T=>(forall z:_p_P_T,((Is_true (_p_P_equal zenon_Tx_u y))->((
Is_true (_p_P_equal y z))->(Is_true (_p_P_equal zenon_Tx_u z))))))
zenon_Ty_v (fun zenon_H21=>(zenon_all _p_P_T (fun z:_p_P_T=>((Is_true (
_p_P_equal zenon_Tx_u zenon_Ty_v))->((Is_true (_p_P_equal zenon_Ty_v z))
->(Is_true (_p_P_equal zenon_Tx_u z))))) zenon_Tz_x (fun zenon_H20=>(
zenon_imply _ _ (fun zenon_H1f=>(zenon_H1f zenon_H1e)) (fun zenon_H1d=>(
zenon_imply _ _ (fun zenon_H1c=>(zenon_H1c zenon_H19)) (fun zenon_H1b=>(
zenon_H18 zenon_H1b)) zenon_H1d)) zenon_H20)) zenon_H21)) zenon_H22))
zenon_H23)))) zenon_H2b)) (zenon_notnot _ (refl_equal (_p_P_equal
zenon_Tx_u zenon_Tz_x))) zenon_H1a)) zenon_H18 zenon_H19)) in (
zenon_noteq _ zenon_Tz_x zenon_H16))))))) zenon_H31)) zenon_H32))
zenon_H33)) zenon_H34)) zenon_H35)) zenon_H36)) zenon_H37)) zenon_G))
in (zenon_notall _p_P_T (fun x:_p_P_T=>(forall y:_p_P_T,(forall z
:_p_P_T,((Is_true (_p_P_equal x y))->((Is_true (_p_P_equal y z))->(
Is_true (_p_P_equal x z))))))) (fun(zenon_Tx_k:_p_P_T) zenon_H12=>(
zenon_notall _p_P_T (fun y:_p_P_T=>(forall z:_p_P_T,((Is_true (
_p_P_equal zenon_Tx_k y))->((Is_true (_p_P_equal y z))->(Is_true (
_p_P_equal zenon_Tx_k z)))))) (fun(zenon_Ty_l:_p_P_T) zenon_H11=>(
zenon_notall _p_P_T (fun z:_p_P_T=>((Is_true (_p_P_equal zenon_Tx_k
zenon_Ty_l))->((Is_true (_p_P_equal zenon_Ty_l z))->(Is_true (
_p_P_equal zenon_Tx_k z))))) (fun(zenon_Tz_n:_p_P_T) zenon_H10=>(
zenon_notimply _ _ (fun zenon_H6 zenon_Hf=>(zenon_notimply _ _ (fun
zenon_H4 zenon_H3=>(zenon_all _p_P_T (fun x:_p_P_T=>(forall y:_p_P_T,(
forall z:_p_P_T,(((Is_true (_p_P_equal x y))/\(Is_true (_p_P_equal y z))
)->(Is_true (_p_P_equal x z)))))) zenon_Tx_k (fun zenon_He=>(zenon_all
_p_P_T (fun y:_p_P_T=>(forall z:_p_P_T,(((Is_true (_p_P_equal
zenon_Tx_k y))/\(Is_true (_p_P_equal y z)))->(Is_true (_p_P_equal
zenon_Tx_k z))))) zenon_Ty_l (fun zenon_Hc=>(zenon_all _p_P_T (fun z
:_p_P_T=>(((Is_true (_p_P_equal zenon_Tx_k zenon_Ty_l))/\(Is_true (
_p_P_equal zenon_Ty_l z)))->(Is_true (_p_P_equal zenon_Tx_k z))))
zenon_Tz_n (fun zenon_H9=>(zenon_imply _ _ (fun zenon_H8=>(zenon_notand
_ _ (fun zenon_H7=>(zenon_H7 zenon_H6)) (fun zenon_H5=>(zenon_H5
zenon_H4)) zenon_H8)) (fun zenon_H2=>(zenon_H3 zenon_H2)) zenon_H9))
zenon_Hc)) zenon_He)) _p_P_equal_transitive)) zenon_Hf)) zenon_H10))
zenon_H11)) zenon_H12)) zenon_H13))))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_transitive :
      forall x  y  z : abst_T,
        Is_true ((abst_equal x y)) ->
          Is_true ((abst_equal y z)) -> Is_true ((abst_equal x z)).
    assert (__force_use_p_P_T := _p_P_T).
    assert (__force_use__p_P_equal := _p_P_equal).
    assert (__force_use__p_P_equal_transitive := _p_P_equal_transitive).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_equal := abst_equal).
    apply for_zenon_equal_transitive;
    auto.
    Qed.
    End Proof_of_equal_transitive.
  
  Theorem equal_transitive  (_p_P_T : Set) (_p_P_equal :
    _p_P_T -> _p_P_T -> basics.bool__t) (_p_P_equal_transitive :
    forall x  y  z : _p_P_T,
      (Is_true ((_p_P_equal x y)) /\ Is_true ((_p_P_equal y z))) ->
        Is_true ((_p_P_equal x z)))
    (abst_T := _p_P_T) (abst_equal := equal _p_P_T _p_P_equal):
    forall x  y  z : abst_T,
      Is_true ((abst_equal x y)) ->
        Is_true ((abst_equal y z)) -> Is_true ((abst_equal x z)).
  apply for_zenon_abstracted_equal_transitive;
  auto.
  Qed.
  
  (* From species num_capteur#Imp_capteur. *)
  (* Section for proof of theorem 'all_field_different_0_1'. *)
  Section Proof_of_all_field_different_0_1.
    Variable _p_P_T : Set.
    Variable _p_P_equal : _p_P_T -> _p_P_T -> basics.bool__t.
    Variable _p_P_s : _p_P_T -> _p_P_T.
    Variable _p_P_zero : _p_P_T.
    Variable _p_P_zero_is_not_successor :
      forall x : _p_P_T, ~Is_true ((_p_P_equal _p_P_zero (_p_P_s x))).
    Let abst_T := _p_P_T.
    Let abst_capt_1 := capt_1 _p_P_T _p_P_zero.
    Let abst_equal := equal _p_P_T _p_P_equal.
    Let abst_capt_2 := capt_2 _p_P_T _p_P_s
    abst_capt_1.
(* File "num_capteur.fcl", line 77, character 4, line 78, character 36 *)
Theorem for_zenon_all_field_different_0_1:(~(Is_true (abst_equal
abst_capt_1 abst_capt_2))).
Proof.
exact(
let zenon_L1_:((~(abst_capt_1 = _p_P_zero))->False):=
(fun zenon_H2:(~(abst_capt_1 = _p_P_zero))=>(let zenon_H3:=zenon_H2 in (
zenon_noteq _ _p_P_zero zenon_H3)))in
(NNPP _ (fun zenon_G=>(zenon_G (fun zenon_H9=>(let zenon_H5:=zenon_H9
in (zenon_all _p_P_T (fun x:_p_P_T=>(~(Is_true (_p_P_equal _p_P_zero (
_p_P_s x))))) _p_P_zero (fun zenon_H4=>(zenon_subst _ (fun zenon_Vf=>(
Is_true zenon_Vf)) (_p_P_equal abst_capt_1 abst_capt_2) (_p_P_equal
_p_P_zero (_p_P_s _p_P_zero)) (fun zenon_H6=>(zenon_subst _ (fun
zenon_Vi=>(~((_p_P_equal zenon_Vi abst_capt_2) = (_p_P_equal _p_P_zero (
_p_P_s _p_P_zero))))) abst_capt_1 _p_P_zero (fun zenon_H2=>(zenon_L1_
zenon_H2)) (zenon_subst _ (fun zenon_Vg=>(~((_p_P_equal _p_P_zero
zenon_Vg) = (_p_P_equal _p_P_zero (_p_P_s _p_P_zero))))) abst_capt_2 (
_p_P_s _p_P_zero) (fun zenon_H8=>(let zenon_H7:=zenon_H8 in (
zenon_subst _ (fun zenon_Vh=>(~((_p_P_s zenon_Vh) = (_p_P_s _p_P_zero)))
) abst_capt_1 _p_P_zero (fun zenon_H2=>(zenon_L1_ zenon_H2)) (
zenon_notnot _ (refl_equal (_p_P_s _p_P_zero))) zenon_H7))) (
zenon_notnot _ (refl_equal (_p_P_equal _p_P_zero (_p_P_s _p_P_zero)))))
zenon_H6)) zenon_H4 zenon_H5)) _p_P_zero_is_not_successor))))))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_all_field_different_0_1 :
      ~Is_true (((abst_equal abst_capt_1 abst_capt_2))).
    assert (__force_use_p_P_T := _p_P_T).
    assert (__force_use__p_P_equal := _p_P_equal).
    assert (__force_use__p_P_s := _p_P_s).
    assert (__force_use__p_P_zero := _p_P_zero).
    assert (__force_use__p_P_zero_is_not_successor :=
      _p_P_zero_is_not_successor).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_capt_1 := abst_capt_1).
    assert (__force_use_abst_equal := abst_equal).
    assert (__force_use_abst_capt_2 := abst_capt_2).
    apply for_zenon_all_field_different_0_1;
    auto.
    Qed.
    End Proof_of_all_field_different_0_1.
  
  Theorem all_field_different_0_1  (_p_P_T : Set) (_p_P_equal :
    _p_P_T -> _p_P_T -> basics.bool__t) (_p_P_s : _p_P_T -> _p_P_T)
    (_p_P_zero : _p_P_T) (_p_P_zero_is_not_successor :
    forall x : _p_P_T, ~Is_true ((_p_P_equal _p_P_zero (_p_P_s x))))
    (abst_T := _p_P_T) (abst_capt_1 := capt_1 _p_P_T _p_P_zero)
    (abst_equal := equal _p_P_T _p_P_equal) (abst_capt_2 := capt_2 _p_P_T
    _p_P_s abst_capt_1): ~Is_true (((abst_equal abst_capt_1 abst_capt_2))).
  apply for_zenon_abstracted_all_field_different_0_1;
  auto.
  Qed.
  Definition capt_3 (_p_P_T : Set) (_p_P_s : _p_P_T -> _p_P_T)
    (abst_T := _p_P_T) (abst_capt_2 : abst_T) : abst_T :=
    (_p_P_s abst_capt_2).
  
  (* From species num_capteur#Imp_capteur. *)
  (* Section for proof of theorem 'all_field_different_0_2'. *)
  Section Proof_of_all_field_different_0_2.
    Variable _p_P_T : Set.
    Variable _p_P_equal : _p_P_T -> _p_P_T -> basics.bool__t.
    Variable _p_P_s : _p_P_T -> _p_P_T.
    Variable _p_P_zero : _p_P_T.
    Variable _p_P_zero_is_not_successor :
      forall x : _p_P_T, ~Is_true ((_p_P_equal _p_P_zero (_p_P_s x))).
    Let abst_T := _p_P_T.
    Let abst_capt_1 := capt_1 _p_P_T _p_P_zero.
    Let abst_equal := equal _p_P_T
    _p_P_equal.
    Variable abst_capt_2 : abst_T.
    Let abst_capt_3 := capt_3 _p_P_T _p_P_s
    abst_capt_2.
(* File "num_capteur.fcl", line 82, character 4, line 83, character 36 *)
Theorem for_zenon_all_field_different_0_2:(~(Is_true (abst_equal
abst_capt_1 abst_capt_3))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G (fun zenon_H9=>(let zenon_H3:=zenon_H9
in (zenon_all _p_P_T (fun x:_p_P_T=>(~(Is_true (_p_P_equal _p_P_zero (
_p_P_s x))))) abst_capt_2 (fun zenon_H2=>(zenon_subst _ (fun zenon_Vf=>(
Is_true zenon_Vf)) (_p_P_equal abst_capt_1 abst_capt_3) (_p_P_equal
_p_P_zero (_p_P_s abst_capt_2)) (fun zenon_H4=>(zenon_subst _ (fun
zenon_Vh=>(~((_p_P_equal zenon_Vh abst_capt_3) = (_p_P_equal _p_P_zero (
_p_P_s abst_capt_2))))) abst_capt_1 _p_P_zero (fun zenon_H8=>(let
zenon_H7:=zenon_H8 in (zenon_noteq _ _p_P_zero zenon_H7))) (zenon_subst
_ (fun zenon_Vg=>(~((_p_P_equal _p_P_zero zenon_Vg) = (_p_P_equal
_p_P_zero (_p_P_s abst_capt_2))))) abst_capt_3 (_p_P_s abst_capt_2) (
fun zenon_H6=>(let zenon_H5:=zenon_H6 in (zenon_noteq _ (_p_P_s
abst_capt_2) zenon_H5))) (zenon_notnot _ (refl_equal (_p_P_equal
_p_P_zero (_p_P_s abst_capt_2))))) zenon_H4)) zenon_H2 zenon_H3))
_p_P_zero_is_not_successor))))))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_all_field_different_0_2 :
      ~Is_true (((abst_equal abst_capt_1 abst_capt_3))).
    assert (__force_use_p_P_T := _p_P_T).
    assert (__force_use__p_P_equal := _p_P_equal).
    assert (__force_use__p_P_s := _p_P_s).
    assert (__force_use__p_P_zero := _p_P_zero).
    assert (__force_use__p_P_zero_is_not_successor :=
      _p_P_zero_is_not_successor).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_capt_1 := abst_capt_1).
    assert (__force_use_abst_equal := abst_equal).
    assert (__force_use_abst_capt_2 := abst_capt_2).
    assert (__force_use_abst_capt_3 := abst_capt_3).
    apply for_zenon_all_field_different_0_2;
    auto.
    Qed.
    End Proof_of_all_field_different_0_2.
  
  Theorem all_field_different_0_2  (_p_P_T : Set) (_p_P_equal :
    _p_P_T -> _p_P_T -> basics.bool__t) (_p_P_s : _p_P_T -> _p_P_T)
    (_p_P_zero : _p_P_T) (_p_P_zero_is_not_successor :
    forall x : _p_P_T, ~Is_true ((_p_P_equal _p_P_zero (_p_P_s x))))
    (abst_T := _p_P_T) (abst_capt_1 := capt_1 _p_P_T _p_P_zero)
    (abst_equal := equal _p_P_T _p_P_equal) (abst_capt_2 : abst_T)
    (abst_capt_3 := capt_3 _p_P_T _p_P_s abst_capt_2):
    ~Is_true (((abst_equal abst_capt_1 abst_capt_3))).
  apply for_zenon_abstracted_all_field_different_0_2;
  auto.
  Qed.
  
  (* From species num_capteur#Imp_capteur. *)
  (* Section for proof of theorem 'all_field_different_1_2'. *)
  Section Proof_of_all_field_different_1_2.
    Variable _p_P_T : Set.
    Variable _p_P_equal : _p_P_T -> _p_P_T -> basics.bool__t.
    Variable _p_P_s : _p_P_T -> _p_P_T.
    Variable _p_P_zero : _p_P_T.
    Variable _p_P_succ_is_an_injection :
      forall x  y : _p_P_T,
        Is_true ((_p_P_equal (_p_P_s x) (_p_P_s y))) ->
          Is_true ((_p_P_equal x y)).
    Variable _p_P_zero_is_not_successor :
      forall x : _p_P_T, ~Is_true ((_p_P_equal _p_P_zero (_p_P_s x))).
    Let abst_T := _p_P_T.
    Let abst_capt_1 := capt_1 _p_P_T _p_P_zero.
    Let abst_equal := equal _p_P_T _p_P_equal.
    Let abst_capt_2 := capt_2 _p_P_T _p_P_s abst_capt_1.
    Let abst_capt_3 := capt_3 _p_P_T _p_P_s
    abst_capt_2.
(* File "num_capteur.fcl", line 87, character 4, line 88, character 60 *)
Theorem for_zenon_all_field_different_1_2:(~(Is_true (abst_equal
abst_capt_2 abst_capt_3))).
Proof.
exact(
let zenon_L1_:((~((_p_P_s abst_capt_1) = (_p_P_s _p_P_zero)))->False):=
(fun zenon_H3:(~((_p_P_s abst_capt_1) = (_p_P_s _p_P_zero)))=>(
zenon_subst _ (fun zenon_Vf=>(~((_p_P_s zenon_Vf) = (_p_P_s _p_P_zero)))
) abst_capt_1 _p_P_zero (fun zenon_H5=>(let zenon_H4:=zenon_H5 in (
zenon_noteq _ _p_P_zero zenon_H4))) (zenon_notnot _ (refl_equal (_p_P_s
_p_P_zero))) zenon_H3))in
let zenon_L2_:((~(abst_capt_3 = (_p_P_s (_p_P_s abst_capt_1))))->False):=
(fun zenon_H6:(~(abst_capt_3 = (_p_P_s (_p_P_s abst_capt_1))))=>(let
zenon_H7:=zenon_H6 in (zenon_subst _ (fun zenon_Vg=>(~((_p_P_s zenon_Vg)
 = (_p_P_s (_p_P_s abst_capt_1))))) abst_capt_2 (_p_P_s abst_capt_1) (
fun zenon_H9=>(let zenon_H8:=zenon_H9 in (zenon_noteq _ (_p_P_s
abst_capt_1) zenon_H8))) (zenon_notnot _ (refl_equal (_p_P_s (_p_P_s
abst_capt_1)))) zenon_H7)))in
(NNPP _ (fun zenon_G=>(zenon_G (fun zenon_H13=>(let zenon_He:=zenon_H13
in (zenon_all _p_P_T (fun x:_p_P_T=>(~(Is_true (_p_P_equal _p_P_zero (
_p_P_s x))))) _p_P_zero (fun zenon_Ha=>(zenon_all _p_P_T (fun x:_p_P_T=>
(forall y:_p_P_T,((Is_true (_p_P_equal (_p_P_s x) (_p_P_s y)))->(
Is_true (_p_P_equal x y))))) _p_P_zero (fun zenon_H12=>(zenon_all
_p_P_T (fun y:_p_P_T=>((Is_true (_p_P_equal (_p_P_s _p_P_zero) (_p_P_s
y)))->(Is_true (_p_P_equal _p_P_zero y)))) (_p_P_s abst_capt_1) (fun
zenon_H11=>(zenon_imply _ _ (fun zenon_Hd=>(zenon_subst _ (fun
zenon_Vj=>(Is_true zenon_Vj)) (_p_P_equal abst_capt_2 abst_capt_3) (
_p_P_equal (_p_P_s _p_P_zero) (_p_P_s (_p_P_s abst_capt_1))) (fun
zenon_Hf=>(zenon_subst _ (fun zenon_Vl=>(~((_p_P_equal zenon_Vl
abst_capt_3) = (_p_P_equal (_p_P_s _p_P_zero) (_p_P_s (_p_P_s
abst_capt_1)))))) abst_capt_2 (_p_P_s _p_P_zero) (fun zenon_H10=>(let
zenon_H3:=zenon_H10 in (zenon_L1_ zenon_H3))) (zenon_subst _ (fun
zenon_Vk=>(~((_p_P_equal (_p_P_s _p_P_zero) zenon_Vk) = (_p_P_equal (
_p_P_s _p_P_zero) (_p_P_s (_p_P_s abst_capt_1)))))) abst_capt_3 (_p_P_s
(_p_P_s abst_capt_1)) (fun zenon_H6=>(zenon_L2_ zenon_H6)) (
zenon_notnot _ (refl_equal (_p_P_equal (_p_P_s _p_P_zero) (_p_P_s (
_p_P_s abst_capt_1)))))) zenon_Hf)) zenon_Hd zenon_He)) (fun zenon_Hb=>(
zenon_subst _ (fun zenon_Vh=>(Is_true zenon_Vh)) (_p_P_equal _p_P_zero (
_p_P_s abst_capt_1)) (_p_P_equal _p_P_zero (_p_P_s _p_P_zero)) (fun
zenon_Hc=>(zenon_subst _ (fun zenon_Vi=>(~((_p_P_equal _p_P_zero
zenon_Vi) = (_p_P_equal _p_P_zero (_p_P_s _p_P_zero))))) (_p_P_s
abst_capt_1) (_p_P_s _p_P_zero) (fun zenon_H3=>(zenon_L1_ zenon_H3)) (
zenon_notnot _ (refl_equal (_p_P_equal _p_P_zero (_p_P_s _p_P_zero))))
zenon_Hc)) zenon_Ha zenon_Hb)) zenon_H11)) zenon_H12))
_p_P_succ_is_an_injection)) _p_P_zero_is_not_successor))))))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_all_field_different_1_2 :
      ~Is_true (((abst_equal abst_capt_2 abst_capt_3))).
    assert (__force_use_p_P_T := _p_P_T).
    assert (__force_use__p_P_equal := _p_P_equal).
    assert (__force_use__p_P_s := _p_P_s).
    assert (__force_use__p_P_zero := _p_P_zero).
    assert (__force_use__p_P_succ_is_an_injection :=
      _p_P_succ_is_an_injection).
    assert (__force_use__p_P_zero_is_not_successor :=
      _p_P_zero_is_not_successor).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_capt_1 := abst_capt_1).
    assert (__force_use_abst_equal := abst_equal).
    assert (__force_use_abst_capt_2 := abst_capt_2).
    assert (__force_use_abst_capt_3 := abst_capt_3).
    apply for_zenon_all_field_different_1_2;
    auto.
    Qed.
    End Proof_of_all_field_different_1_2.
  
  Theorem all_field_different_1_2  (_p_P_T : Set) (_p_P_equal :
    _p_P_T -> _p_P_T -> basics.bool__t) (_p_P_s : _p_P_T -> _p_P_T)
    (_p_P_zero : _p_P_T) (_p_P_succ_is_an_injection :
    forall x  y : _p_P_T,
      Is_true ((_p_P_equal (_p_P_s x) (_p_P_s y))) ->
        Is_true ((_p_P_equal x y)))
    (_p_P_zero_is_not_successor :
    forall x : _p_P_T, ~Is_true ((_p_P_equal _p_P_zero (_p_P_s x))))
    (abst_T := _p_P_T) (abst_capt_1 := capt_1 _p_P_T _p_P_zero)
    (abst_equal := equal _p_P_T _p_P_equal) (abst_capt_2 := capt_2 _p_P_T
    _p_P_s abst_capt_1) (abst_capt_3 := capt_3 _p_P_T _p_P_s abst_capt_2):
    ~Is_true (((abst_equal abst_capt_2 abst_capt_3))).
  apply for_zenon_abstracted_all_field_different_1_2;
  auto.
  Qed.
  
  (* From species num_capteur#Imp_capteur. *)
  Theorem all_value  (_p_P_T : Set) (abst_T : Set) (abst_capt_1 : abst_T)
    (abst_equal : abst_T -> abst_T -> basics.bool__t) (abst_capt_2 : abst_T)
    (abst_capt_3 : abst_T):
    forall e : abst_T,
      Is_true ((abst_equal e abst_capt_1)) \/
        Is_true ((abst_equal e abst_capt_2)) \/
          Is_true ((abst_equal e abst_capt_3)).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  Definition print (_p_P_T : Set) (abst_T : Set) (abst_capt_1 : abst_T)
    (abst_equal : abst_T -> abst_T -> basics.bool__t) (abst_capt_2 : abst_T)
    (abst_capt_3 : abst_T) (x : abst_T) : basics.string__t :=
    (if (abst_equal x abst_capt_1) then "capt_1"%string
      else (if (abst_equal x abst_capt_2) then "capt_2"%string
             else (if (abst_equal x abst_capt_3) then "capt_3"%string
                    else "Erreur capteur"%string))).
  
  (* Fully defined 'Imp_capteur' species's collection generator. *)
  Definition collection_create (_p_P_T : Set) _p_P_equal _p_P_s _p_P_zero
    _p_P_equal_reflexive _p_P_equal_symmetric _p_P_equal_transitive
    _p_P_succ_is_an_injection _p_P_zero_is_not_successor :=
    let local_rep := _p_P_T in
    (* From species num_capteur#Imp_capteur. *)
    let local_capt_1 := capt_1 _p_P_T _p_P_zero in
    (* From species num_capteur#Imp_capteur. *)
    let local_equal := equal _p_P_T _p_P_equal in
    (* From species basics#Basic_object. *)
    let local_parse := basics.Basic_object.parse local_rep in
    (* From species num_capteur#Imp_capteur. *)
    let local_capt_2 := capt_2 _p_P_T _p_P_s local_capt_1 in
    (* From species num_capteur#Imp_capteur. *)
    let local_element := element _p_P_T local_rep local_capt_1 in
    (* From species sets#Setoid. *)
    let local_different := sets.Setoid.different local_rep local_equal in
    (* From species num_capteur#Imp_capteur. *)
    let local_equal_reflexive := equal_reflexive _p_P_T _p_P_equal
      _p_P_equal_reflexive in
    (* From species num_capteur#Imp_capteur. *)
    let local_equal_symmetric := equal_symmetric _p_P_T _p_P_equal
      _p_P_equal_symmetric in
    (* From species num_capteur#Imp_capteur. *)
    let local_equal_transitive := equal_transitive _p_P_T _p_P_equal
      _p_P_equal_transitive in
    (* From species num_capteur#Imp_capteur. *)
    let local_all_field_different_0_1 := all_field_different_0_1 _p_P_T
      _p_P_equal _p_P_s _p_P_zero _p_P_zero_is_not_successor in
    (* From species num_capteur#Imp_capteur. *)
    let local_capt_3 := capt_3 _p_P_T _p_P_s local_capt_2 in
    (* From species sets#Setoid. *)
    let local_same_is_not_different := sets.Setoid.same_is_not_different
      local_rep local_equal in
    (* From species num_capteur#Imp_capteur. *)
    let local_all_field_different_0_2 := all_field_different_0_2 _p_P_T
      _p_P_equal _p_P_s _p_P_zero _p_P_zero_is_not_successor local_capt_2 in
    (* From species num_capteur#Imp_capteur. *)
    let local_all_field_different_1_2 := all_field_different_1_2 _p_P_T
      _p_P_equal _p_P_s _p_P_zero _p_P_succ_is_an_injection
      _p_P_zero_is_not_successor in
    (* From species num_capteur#Imp_capteur. *)
    let local_all_value := all_value _p_P_T local_rep local_capt_1
      local_equal local_capt_2 local_capt_3 in
    (* From species num_capteur#Imp_capteur. *)
    let local_print := print _p_P_T local_rep local_capt_1 local_equal
      local_capt_2 local_capt_3 in
    (* From species sets#Setoid. *)
    let local_different_is_complete := sets.Setoid.different_is_complete
      local_rep local_equal local_different local_equal_reflexive
      local_equal_symmetric local_equal_transitive
      local_same_is_not_different in
    (* From species sets#Setoid. *)
    let local_different_is_irreflexive :=
      sets.Setoid.different_is_irreflexive local_rep local_equal
      local_different local_equal_reflexive local_same_is_not_different in
    (* From species sets#Setoid. *)
    let local_different_is_symmetric := sets.Setoid.different_is_symmetric
      local_rep local_equal local_different local_equal_symmetric
      local_same_is_not_different in
    mk_record (_p_P_T : Set) local_rep local_capt_1 local_equal local_parse
    local_capt_2 local_element local_different local_equal_reflexive
    local_equal_symmetric local_equal_transitive
    local_all_field_different_0_1 local_capt_3 local_same_is_not_different
    local_all_field_different_0_2 local_all_field_different_1_2
    local_all_value local_print local_different_is_complete
    local_different_is_irreflexive local_different_is_symmetric.
  
End Imp_capteur.

Module Coll_capteur.
  Let effective_collection := Imp_capteur.collection_create
    peano.Coll_peano.me_as_carrier peano.Coll_peano.equal peano.Coll_peano.s
    peano.Coll_peano.zero peano.Coll_peano.equal_reflexive
    peano.Coll_peano.equal_symmetric peano.Coll_peano.equal_transitive
    peano.Coll_peano.succ_is_an_injection
    peano.Coll_peano.zero_is_not_successor.
  (* Carrier's structure explicitly given by "rep". *)
  Definition me_as_carrier := peano.Coll_peano.me_as_carrier.
  Definition capt_1 := effective_collection.(Imp_capteur.rf_capt_1 _).
  Definition equal := effective_collection.(Imp_capteur.rf_equal _).
  Definition parse := effective_collection.(Imp_capteur.rf_parse _).
  Definition capt_2 := effective_collection.(Imp_capteur.rf_capt_2 _).
  Definition element := effective_collection.(Imp_capteur.rf_element _).
  Definition different := effective_collection.(Imp_capteur.rf_different _).
  Definition equal_reflexive :=
    effective_collection.(Imp_capteur.rf_equal_reflexive _).
  Definition equal_symmetric :=
    effective_collection.(Imp_capteur.rf_equal_symmetric _).
  Definition equal_transitive :=
    effective_collection.(Imp_capteur.rf_equal_transitive _).
  Definition all_field_different_0_1 :=
    effective_collection.(Imp_capteur.rf_all_field_different_0_1 _).
  Definition capt_3 := effective_collection.(Imp_capteur.rf_capt_3 _).
  Definition same_is_not_different :=
    effective_collection.(Imp_capteur.rf_same_is_not_different _).
  Definition all_field_different_0_2 :=
    effective_collection.(Imp_capteur.rf_all_field_different_0_2 _).
  Definition all_field_different_1_2 :=
    effective_collection.(Imp_capteur.rf_all_field_different_1_2 _).
  Definition all_value := effective_collection.(Imp_capteur.rf_all_value _).
  Definition print := effective_collection.(Imp_capteur.rf_print _).
  Definition different_is_complete :=
    effective_collection.(Imp_capteur.rf_different_is_complete _).
  Definition different_is_irreflexive :=
    effective_collection.(Imp_capteur.rf_different_is_irreflexive _).
  Definition different_is_symmetric :=
    effective_collection.(Imp_capteur.rf_different_is_symmetric _).
  
End Coll_capteur.

