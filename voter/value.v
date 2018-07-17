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
Require basic_type.
Module Sp_value_tol.
  
End Sp_value_tol.

Module Imp_value_tol.
  Definition consistency_rule (_p_T_T : Set) (_p_T_geq :
    _p_T_T -> _p_T_T -> basics.bool__t) (_p_T_plus :
    _p_T_T -> _p_T_T -> _p_T_T) (_p_tol_tol : _p_T_T) (abst_T := _p_T_T)
    (x : abst_T) (y : abst_T) : basics.bool__t :=
    (if (_p_T_geq x y) then (_p_T_geq (_p_T_plus y _p_tol_tol) x)
      else (_p_T_geq (_p_T_plus x _p_tol_tol) y)).
  Definition element (_p_T_T : Set) (_p_T_element : _p_T_T)
    (abst_T := _p_T_T) : abst_T := _p_T_element.
  Definition equal (_p_T_T : Set) (_p_T_equal :
    _p_T_T -> _p_T_T -> basics.bool__t) (abst_T := _p_T_T) (x : abst_T)
    (y : abst_T) : basics.bool__t := (_p_T_equal x y).
  Definition parse (_p_T_T : Set) (_p_T_parse : basics.string__t -> _p_T_T)
    (abst_T := _p_T_T) (x : basics.string__t) : abst_T := (_p_T_parse x).
  Definition print (_p_T_T : Set) (_p_T_print : _p_T_T -> basics.string__t)
    (abst_T := _p_T_T) (x : abst_T) : basics.string__t := (_p_T_print x).
  
  (* From species value#Imp_value_tol. *)
  (* Section for proof of theorem 'consistency_rule_reflexive'. *)
  Section Proof_of_consistency_rule_reflexive.
    Variable _p_T_T : Set.
    Variable _p_T_geq : _p_T_T -> _p_T_T -> basics.bool__t.
    Variable _p_T_plus : _p_T_T -> _p_T_T -> _p_T_T.
    Variable _p_tol_tol : _p_T_T.
    Let abst_T := _p_T_T.
    Let abst_consistency_rule := consistency_rule _p_T_T _p_T_geq _p_T_plus
    _p_tol_tol.
    Section __A_1.
      Variable x : abst_T.
      (* Theorem's body. *)
      Theorem __A_1_LEMMA : Is_true ((_p_T_geq (_p_T_plus x _p_tol_tol) x)).
      assert (__force_use_x := x).
      (* Proof was flagged as assumed. *)
      apply coq_builtins.magic_prove.
      Qed.
      End __A_1.
(* File "value.fcl", line 82, characters 11-54 *)
Theorem for_zenon_consistency_rule_reflexive:(forall a:abst_T,(Is_true (
abst_consistency_rule a a))).
Proof.
exact(
let zenon_L1_:(forall zenon_Ta_c:abst_T,((~(Is_true (_p_T_geq (
_p_T_plus zenon_Ta_c _p_tol_tol) zenon_Ta_c)))->False)):=
(fun(zenon_Ta_c:abst_T)(zenon_H3:(~(Is_true (_p_T_geq (_p_T_plus
zenon_Ta_c _p_tol_tol) zenon_Ta_c))))=>(zenon_all abst_T (fun x:abst_T=>
(Is_true (_p_T_geq (_p_T_plus x _p_tol_tol) x))) zenon_Ta_c (fun
zenon_H4=>(zenon_H3 zenon_H4)) __A_1_LEMMA))in
(NNPP _ (fun zenon_G=>(zenon_notallex (fun a:abst_T=>(Is_true (
abst_consistency_rule a a))) (fun zenon_H9=>(zenon_ex abst_T (fun a
:abst_T=>(~(Is_true (abst_consistency_rule a a)))) (fun(zenon_Ta_c
:abst_T) zenon_H8=>(let zenon_H7:=zenon_H8 in (zenon_focal_ite_bool_n (
_p_T_geq zenon_Ta_c zenon_Ta_c) (_p_T_geq (_p_T_plus zenon_Ta_c
_p_tol_tol) zenon_Ta_c) (_p_T_geq (_p_T_plus zenon_Ta_c _p_tol_tol)
zenon_Ta_c) (fun zenon_H5 zenon_H3=>(zenon_L1_ zenon_Ta_c zenon_H3)) (
fun zenon_H6 zenon_H3=>(zenon_L1_ zenon_Ta_c zenon_H3)) zenon_H7)))
zenon_H9)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_consistency_rule_reflexive :
      forall a : abst_T, Is_true ((abst_consistency_rule a a)).
    assert (__force_use_p_T_T := _p_T_T).
    assert (__force_use__p_T_geq := _p_T_geq).
    assert (__force_use__p_T_plus := _p_T_plus).
    assert (__force_use__p_tol_tol := _p_tol_tol).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_consistency_rule := abst_consistency_rule).
    apply for_zenon_consistency_rule_reflexive;
    auto.
    Qed.
    End Proof_of_consistency_rule_reflexive.
  
  Theorem consistency_rule_reflexive  (_p_T_T : Set) (_p_T_geq :
    _p_T_T -> _p_T_T -> basics.bool__t) (_p_T_plus :
    _p_T_T -> _p_T_T -> _p_T_T) (_p_tol_tol : _p_T_T) (abst_T := _p_T_T)
    (abst_consistency_rule := consistency_rule _p_T_T _p_T_geq _p_T_plus
    _p_tol_tol): forall a : abst_T, Is_true ((abst_consistency_rule a a)).
  apply for_zenon_abstracted_consistency_rule_reflexive;
  auto.
  Qed.
  
  (* From species value#Imp_value_tol. *)
  Theorem consistency_rule_symmetric  (_p_T_T : Set) (abst_T : Set)
    (abst_consistency_rule : abst_T -> abst_T -> basics.bool__t):
    forall a  b : abst_T,
      Is_true ((abst_consistency_rule a b)) ->
        Is_true ((abst_consistency_rule b a)).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
  (* From species value#Imp_value_tol. *)
  (* Section for proof of theorem 'equal_reflexive'. *)
  Section Proof_of_equal_reflexive.
    Variable _p_T_T : Set.
    Variable _p_T_equal : _p_T_T -> _p_T_T -> basics.bool__t.
    Variable _p_T_equal_reflexive :
      forall x : _p_T_T, Is_true ((_p_T_equal x x)).
    Let abst_T := _p_T_T.
    Let abst_equal := equal _p_T_T
    _p_T_equal.
(* File "value.fcl", line 75, characters 4-53 *)
Theorem for_zenon_equal_reflexive:(forall x:abst_T,(Is_true (abst_equal
x x))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>(Is_true (
abst_equal x x))) (fun zenon_H6=>(zenon_ex abst_T (fun x:abst_T=>(~(
Is_true (abst_equal x x)))) (fun(zenon_Tx_e:abst_T) zenon_H5=>(let
zenon_H3:=zenon_H5 in (zenon_all _p_T_T (fun x:_p_T_T=>(Is_true (
_p_T_equal x x))) zenon_Tx_e (fun zenon_H2=>(zenon_H3 zenon_H2))
_p_T_equal_reflexive))) zenon_H6)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_reflexive :
      forall x : abst_T, Is_true ((abst_equal x x)).
    assert (__force_use_p_T_T := _p_T_T).
    assert (__force_use__p_T_equal := _p_T_equal).
    assert (__force_use__p_T_equal_reflexive := _p_T_equal_reflexive).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_equal := abst_equal).
    apply for_zenon_equal_reflexive;
    auto.
    Qed.
    End Proof_of_equal_reflexive.
  
  Theorem equal_reflexive  (_p_T_T : Set) (_p_T_equal :
    _p_T_T -> _p_T_T -> basics.bool__t) (_p_T_equal_reflexive :
    forall x : _p_T_T, Is_true ((_p_T_equal x x))) (abst_T := _p_T_T)
    (abst_equal := equal _p_T_T _p_T_equal):
    forall x : abst_T, Is_true ((abst_equal x x)).
  apply for_zenon_abstracted_equal_reflexive;
  auto.
  Qed.
  
  (* From species value#Imp_value_tol. *)
  (* Section for proof of theorem 'equal_symmetric'. *)
  Section Proof_of_equal_symmetric.
    Variable _p_T_T : Set.
    Variable _p_T_equal : _p_T_T -> _p_T_T -> basics.bool__t.
    Variable _p_T_equal_symmetric :
      forall x  y : _p_T_T,
        Is_true ((_p_T_equal x y)) -> Is_true ((_p_T_equal y x)).
    Let abst_T := _p_T_T.
    Let abst_equal := equal _p_T_T
    _p_T_equal.
(* File "value.fcl", line 72, characters 4-53 *)
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
let zenon_H4:=zenon_Ha in (zenon_all _p_T_T (fun x:_p_T_T=>(forall y
:_p_T_T,((Is_true (_p_T_equal x y))->(Is_true (_p_T_equal y x)))))
zenon_Tx_c (fun zenon_H8=>(zenon_all _p_T_T (fun y:_p_T_T=>((Is_true (
_p_T_equal zenon_Tx_c y))->(Is_true (_p_T_equal y zenon_Tx_c))))
zenon_Ty_j (fun zenon_H7=>(zenon_imply _ _ (fun zenon_H6=>(zenon_H6
zenon_H5)) (fun zenon_H3=>(zenon_H4 zenon_H3)) zenon_H7)) zenon_H8))
_p_T_equal_symmetric)))) zenon_Hc)) zenon_Hd)) zenon_He)) zenon_Hf))
zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_symmetric :
      forall x  y : abst_T,
        Is_true ((abst_equal x y)) -> Is_true ((abst_equal y x)).
    assert (__force_use_p_T_T := _p_T_T).
    assert (__force_use__p_T_equal := _p_T_equal).
    assert (__force_use__p_T_equal_symmetric := _p_T_equal_symmetric).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_equal := abst_equal).
    apply for_zenon_equal_symmetric;
    auto.
    Qed.
    End Proof_of_equal_symmetric.
  
  Theorem equal_symmetric  (_p_T_T : Set) (_p_T_equal :
    _p_T_T -> _p_T_T -> basics.bool__t) (_p_T_equal_symmetric :
    forall x  y : _p_T_T,
      Is_true ((_p_T_equal x y)) -> Is_true ((_p_T_equal y x)))
    (abst_T := _p_T_T) (abst_equal := equal _p_T_T _p_T_equal):
    forall x  y : abst_T,
      Is_true ((abst_equal x y)) -> Is_true ((abst_equal y x)).
  apply for_zenon_abstracted_equal_symmetric;
  auto.
  Qed.
  
  (* From species value#Imp_value_tol. *)
  (* Section for proof of theorem 'equal_transitive'. *)
  Section Proof_of_equal_transitive.
    Variable _p_T_T : Set.
    Variable _p_T_equal : _p_T_T -> _p_T_T -> basics.bool__t.
    Variable _p_T_equal_transitive :
      forall x  y  z : _p_T_T,
        Is_true ((_p_T_equal x y)) ->
          Is_true ((_p_T_equal y z)) -> Is_true ((_p_T_equal x z)).
    Let abst_T := _p_T_T.
    Let abst_equal := equal _p_T_T
    _p_T_equal.
(* File "value.fcl", line 69, characters 4-54 *)
Theorem for_zenon_equal_transitive:(forall x:abst_T,(forall y:abst_T,(
forall z:abst_T,((Is_true (abst_equal x y))->((Is_true (abst_equal y z))
->(Is_true (abst_equal x z))))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>(forall y:abst_T,(
forall z:abst_T,((Is_true (abst_equal x y))->((Is_true (abst_equal y z))
->(Is_true (abst_equal x z))))))) (fun zenon_H24=>(zenon_ex abst_T (fun
x:abst_T=>(~(forall y:abst_T,(forall z:abst_T,((Is_true (abst_equal x y)
)->((Is_true (abst_equal y z))->(Is_true (abst_equal x z)))))))) (fun(
zenon_Tx_c:abst_T) zenon_H23=>(zenon_notallex (fun y:abst_T=>(forall z
:abst_T,((Is_true (abst_equal zenon_Tx_c y))->((Is_true (abst_equal y z)
)->(Is_true (abst_equal zenon_Tx_c z)))))) (fun zenon_H22=>(zenon_ex
abst_T (fun y:abst_T=>(~(forall z:abst_T,((Is_true (abst_equal
zenon_Tx_c y))->((Is_true (abst_equal y z))->(Is_true (abst_equal
zenon_Tx_c z))))))) (fun(zenon_Ty_d:abst_T) zenon_H21=>(zenon_notallex (
fun z:abst_T=>((Is_true (abst_equal zenon_Tx_c zenon_Ty_d))->((Is_true (
abst_equal zenon_Ty_d z))->(Is_true (abst_equal zenon_Tx_c z))))) (fun
zenon_H20=>(zenon_ex abst_T (fun z:abst_T=>(~((Is_true (abst_equal
zenon_Tx_c zenon_Ty_d))->((Is_true (abst_equal zenon_Ty_d z))->(Is_true
(abst_equal zenon_Tx_c z)))))) (fun(zenon_Tz_f:abst_T) zenon_H1f=>(
zenon_notimply _ _ (fun zenon_H1d zenon_H1e=>(zenon_notimply _ _ (fun
zenon_H1c zenon_H1b=>(let zenon_Hc:=zenon_H1d in (let zenon_H7
:=zenon_H1c in (let zenon_H6:=zenon_H1b in (let zenon_H18:=(fun
zenon_H1a=>(zenon_and _ _ (fun zenon_H16 zenon_Hd=>(zenon_Hd zenon_Hc))
zenon_H1a)) in (let zenon_H4:=(fun zenon_H19=>(zenon_subst _ (fun
zenon_Vf=>(Is_true zenon_Vf)) (_p_T_equal zenon_Ty_d zenon_Tz_f) (
_p_T_equal zenon_Tx_c zenon_Tz_f) (fun zenon_H8=>(zenon_subst _ (fun
zenon_Vg=>(~((_p_T_equal zenon_Vg zenon_Tz_f) = (_p_T_equal zenon_Tx_c
zenon_Tz_f)))) zenon_Ty_d zenon_Tx_c (fun zenon_H13=>(zenon_notand _ _ (
fun zenon_H17=>(zenon_H17 (fun zenon_H15=>(let zenon_H12:=(fun
zenon_H14=>(zenon_subst _ (fun zenon_Vh=>(zenon_Vh = zenon_Tx_c))
zenon_Tx_c zenon_Ty_d (fun zenon_H16=>(zenon_H16 zenon_H15)) zenon_H13
zenon_H14)) in (zenon_noteq _ zenon_Tx_c zenon_H12))))) (fun zenon_H11=>
(zenon_H11 (fun zenon_Hc=>(zenon_all _p_T_T (fun x:_p_T_T=>(forall y
:_p_T_T,(forall z:_p_T_T,((Is_true (_p_T_equal x y))->((Is_true (
_p_T_equal y z))->(Is_true (_p_T_equal x z))))))) zenon_Tx_c (fun
zenon_H10=>(zenon_all _p_T_T (fun y:_p_T_T=>(forall z:_p_T_T,((Is_true (
_p_T_equal zenon_Tx_c y))->((Is_true (_p_T_equal y z))->(Is_true (
_p_T_equal zenon_Tx_c z)))))) zenon_Ty_d (fun zenon_Hf=>(zenon_all
_p_T_T (fun z:_p_T_T=>((Is_true (_p_T_equal zenon_Tx_c zenon_Ty_d))->((
Is_true (_p_T_equal zenon_Ty_d z))->(Is_true (_p_T_equal zenon_Tx_c z)))
)) zenon_Tz_f (fun zenon_He=>(zenon_imply _ _ (fun zenon_Hd=>(zenon_Hd
zenon_Hc)) (fun zenon_Hb=>(zenon_imply _ _ (fun zenon_Ha=>(zenon_Ha
zenon_H7)) (fun zenon_H9=>(zenon_H6 zenon_H9)) zenon_Hb)) zenon_He))
zenon_Hf)) zenon_H10)) _p_T_equal_transitive)))) zenon_H18)) (
zenon_notnot _ (refl_equal (_p_T_equal zenon_Tx_c zenon_Tz_f)))
zenon_H8)) zenon_H6 zenon_H7)) in (zenon_noteq _ zenon_Tz_f zenon_H4))))
))) zenon_H1e)) zenon_H1f)) zenon_H20)) zenon_H21)) zenon_H22))
zenon_H23)) zenon_H24)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_transitive :
      forall x  y  z : abst_T,
        Is_true ((abst_equal x y)) ->
          Is_true ((abst_equal y z)) -> Is_true ((abst_equal x z)).
    assert (__force_use_p_T_T := _p_T_T).
    assert (__force_use__p_T_equal := _p_T_equal).
    assert (__force_use__p_T_equal_transitive := _p_T_equal_transitive).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_equal := abst_equal).
    apply for_zenon_equal_transitive;
    auto.
    Qed.
    End Proof_of_equal_transitive.
  
  Theorem equal_transitive  (_p_T_T : Set) (_p_T_equal :
    _p_T_T -> _p_T_T -> basics.bool__t) (_p_T_equal_transitive :
    forall x  y  z : _p_T_T,
      Is_true ((_p_T_equal x y)) ->
        Is_true ((_p_T_equal y z)) -> Is_true ((_p_T_equal x z)))
    (abst_T := _p_T_T) (abst_equal := equal _p_T_T _p_T_equal):
    forall x  y  z : abst_T,
      Is_true ((abst_equal x y)) ->
        Is_true ((abst_equal y z)) -> Is_true ((abst_equal x z)).
  apply for_zenon_abstracted_equal_transitive;
  auto.
  Qed.
  
End Imp_value_tol.

Module Sp_value.
  
End Sp_value.

Module Imp_value.
  Record me_as_species (T_T : Set) : Type :=
    mk_record {
    rf_T : Set ;
    (* From species value#Imp_value. *)
    rf_consistency_rule : rf_T -> rf_T -> basics.bool__t ;
    (* From species value#Imp_value. *)
    rf_element : rf_T ;
    (* From species value#Imp_value. *)
    rf_equal : rf_T -> rf_T -> basics.bool__t ;
    (* From species value#Imp_value. *)
    rf_parse : basics.string__t -> rf_T ;
    (* From species value#Imp_value. *)
    rf_print : rf_T -> basics.string__t ;
    (* From species value#Imp_value. *)
    rf_consistency_rule_reflexive :
      forall a : rf_T, Is_true ((rf_consistency_rule a a)) ;
    (* From species value#Imp_value. *)
    rf_consistency_rule_symmetric :
      forall a  b : rf_T,
        Is_true ((rf_consistency_rule a b)) ->
          Is_true ((rf_consistency_rule b a)) ;
    (* From species sets#Setoid. *)
    rf_different : rf_T -> rf_T -> basics.bool__t ;
    (* From species value#Imp_value. *)
    rf_equal_reflexive : forall x : rf_T, Is_true ((rf_equal x x)) ;
    (* From species value#Imp_value. *)
    rf_equal_symmetric :
      forall x  y : rf_T,
        Is_true ((rf_equal x y)) -> Is_true ((rf_equal y x)) ;
    (* From species value#Imp_value. *)
    rf_equal_transitive :
      forall x  y  z : rf_T,
        Is_true ((rf_equal x y)) ->
          Is_true ((rf_equal y z)) -> Is_true ((rf_equal x z)) ;
    (* From species sets#Setoid. *)
    rf_same_is_not_different :
      forall x  y : rf_T,
        Is_true ((rf_different x y)) <-> ~Is_true (((rf_equal x y))) ;
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
  
  Definition consistency_rule (_p_T_T : Set) (_p_T_equal :
    _p_T_T -> _p_T_T -> basics.bool__t) (abst_T := _p_T_T) (x : abst_T)
    (y : abst_T) : basics.bool__t := (_p_T_equal x y).
  Definition element (_p_T_T : Set) (_p_T_element : _p_T_T)
    (abst_T := _p_T_T) : abst_T := _p_T_element.
  Definition equal (_p_T_T : Set) (_p_T_equal :
    _p_T_T -> _p_T_T -> basics.bool__t) (abst_T := _p_T_T) (x : abst_T)
    (y : abst_T) : basics.bool__t := (_p_T_equal x y).
  Definition parse (_p_T_T : Set) (_p_T_parse : basics.string__t -> _p_T_T)
    (abst_T := _p_T_T) (x : basics.string__t) : abst_T := (_p_T_parse x).
  Definition print (_p_T_T : Set) (_p_T_print : _p_T_T -> basics.string__t)
    (abst_T := _p_T_T) (x : abst_T) : basics.string__t := (_p_T_print x).
  
  (* From species value#Imp_value. *)
  (* Section for proof of theorem 'consistency_rule_reflexive'. *)
  Section Proof_of_consistency_rule_reflexive.
    Variable _p_T_T : Set.
    Variable _p_T_equal : _p_T_T -> _p_T_T -> basics.bool__t.
    Variable _p_T_equal_reflexive :
      forall x : _p_T_T, Is_true ((_p_T_equal x x)).
    Let abst_T := _p_T_T.
    Let abst_consistency_rule := consistency_rule _p_T_T
    _p_T_equal.
(* File "value.fcl", line 145, characters 4-64 *)
Theorem for_zenon_consistency_rule_reflexive:(forall a:abst_T,(Is_true (
abst_consistency_rule a a))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun a:abst_T=>(Is_true (
abst_consistency_rule a a))) (fun zenon_H6=>(zenon_ex abst_T (fun a
:abst_T=>(~(Is_true (abst_consistency_rule a a)))) (fun(zenon_Ta_e
:abst_T) zenon_H5=>(let zenon_H3:=zenon_H5 in (zenon_all _p_T_T (fun x
:_p_T_T=>(Is_true (_p_T_equal x x))) zenon_Ta_e (fun zenon_H2=>(
zenon_H3 zenon_H2)) _p_T_equal_reflexive))) zenon_H6)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_consistency_rule_reflexive :
      forall a : abst_T, Is_true ((abst_consistency_rule a a)).
    assert (__force_use_p_T_T := _p_T_T).
    assert (__force_use__p_T_equal := _p_T_equal).
    assert (__force_use__p_T_equal_reflexive := _p_T_equal_reflexive).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_consistency_rule := abst_consistency_rule).
    apply for_zenon_consistency_rule_reflexive;
    auto.
    Qed.
    End Proof_of_consistency_rule_reflexive.
  
  Theorem consistency_rule_reflexive  (_p_T_T : Set) (_p_T_equal :
    _p_T_T -> _p_T_T -> basics.bool__t) (_p_T_equal_reflexive :
    forall x : _p_T_T, Is_true ((_p_T_equal x x))) (abst_T := _p_T_T)
    (abst_consistency_rule := consistency_rule _p_T_T _p_T_equal):
    forall a : abst_T, Is_true ((abst_consistency_rule a a)).
  apply for_zenon_abstracted_consistency_rule_reflexive;
  auto.
  Qed.
  
  (* From species value#Imp_value. *)
  (* Section for proof of theorem 'consistency_rule_symmetric'. *)
  Section Proof_of_consistency_rule_symmetric.
    Variable _p_T_T : Set.
    Variable _p_T_equal : _p_T_T -> _p_T_T -> basics.bool__t.
    Variable _p_T_equal_symmetric :
      forall x  y : _p_T_T,
        Is_true ((_p_T_equal x y)) -> Is_true ((_p_T_equal y x)).
    Let abst_T := _p_T_T.
    Let abst_consistency_rule := consistency_rule _p_T_T
    _p_T_equal.
(* File "value.fcl", line 143, characters 4-64 *)
Theorem for_zenon_consistency_rule_symmetric:(forall a:abst_T,(forall b
:abst_T,((Is_true (abst_consistency_rule a b))->(Is_true (
abst_consistency_rule b a))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun a:abst_T=>(forall b:abst_T,((
Is_true (abst_consistency_rule a b))->(Is_true (abst_consistency_rule b
a))))) (fun zenon_Hf=>(zenon_ex abst_T (fun a:abst_T=>(~(forall b
:abst_T,((Is_true (abst_consistency_rule a b))->(Is_true (
abst_consistency_rule b a)))))) (fun(zenon_Ta_c:abst_T) zenon_He=>(
zenon_notallex (fun b:abst_T=>((Is_true (abst_consistency_rule
zenon_Ta_c b))->(Is_true (abst_consistency_rule b zenon_Ta_c)))) (fun
zenon_Hd=>(zenon_ex abst_T (fun b:abst_T=>(~((Is_true (
abst_consistency_rule zenon_Ta_c b))->(Is_true (abst_consistency_rule b
zenon_Ta_c))))) (fun(zenon_Tb_j:abst_T) zenon_Hc=>(zenon_notimply _ _ (
fun zenon_Hb zenon_Ha=>(let zenon_H5:=zenon_Hb in (let zenon_H4
:=zenon_Ha in (zenon_all _p_T_T (fun x:_p_T_T=>(forall y:_p_T_T,((
Is_true (_p_T_equal x y))->(Is_true (_p_T_equal y x))))) zenon_Ta_c (
fun zenon_H8=>(zenon_all _p_T_T (fun y:_p_T_T=>((Is_true (_p_T_equal
zenon_Ta_c y))->(Is_true (_p_T_equal y zenon_Ta_c)))) zenon_Tb_j (fun
zenon_H7=>(zenon_imply _ _ (fun zenon_H6=>(zenon_H6 zenon_H5)) (fun
zenon_H3=>(zenon_H4 zenon_H3)) zenon_H7)) zenon_H8))
_p_T_equal_symmetric)))) zenon_Hc)) zenon_Hd)) zenon_He)) zenon_Hf))
zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_consistency_rule_symmetric :
      forall a  b : abst_T,
        Is_true ((abst_consistency_rule a b)) ->
          Is_true ((abst_consistency_rule b a)).
    assert (__force_use_p_T_T := _p_T_T).
    assert (__force_use__p_T_equal := _p_T_equal).
    assert (__force_use__p_T_equal_symmetric := _p_T_equal_symmetric).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_consistency_rule := abst_consistency_rule).
    apply for_zenon_consistency_rule_symmetric;
    auto.
    Qed.
    End Proof_of_consistency_rule_symmetric.
  
  Theorem consistency_rule_symmetric  (_p_T_T : Set) (_p_T_equal :
    _p_T_T -> _p_T_T -> basics.bool__t) (_p_T_equal_symmetric :
    forall x  y : _p_T_T,
      Is_true ((_p_T_equal x y)) -> Is_true ((_p_T_equal y x)))
    (abst_T := _p_T_T) (abst_consistency_rule := consistency_rule _p_T_T
    _p_T_equal):
    forall a  b : abst_T,
      Is_true ((abst_consistency_rule a b)) ->
        Is_true ((abst_consistency_rule b a)).
  apply for_zenon_abstracted_consistency_rule_symmetric;
  auto.
  Qed.
  
  (* From species value#Imp_value. *)
  (* Section for proof of theorem 'equal_reflexive'. *)
  Section Proof_of_equal_reflexive.
    Variable _p_T_T : Set.
    Variable _p_T_equal : _p_T_T -> _p_T_T -> basics.bool__t.
    Variable _p_T_equal_reflexive :
      forall x : _p_T_T, Is_true ((_p_T_equal x x)).
    Let abst_T := _p_T_T.
    Let abst_equal := equal _p_T_T
    _p_T_equal.
(* File "value.fcl", line 137, characters 4-53 *)
Theorem for_zenon_equal_reflexive:(forall x:abst_T,(Is_true (abst_equal
x x))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>(Is_true (
abst_equal x x))) (fun zenon_H6=>(zenon_ex abst_T (fun x:abst_T=>(~(
Is_true (abst_equal x x)))) (fun(zenon_Tx_e:abst_T) zenon_H5=>(let
zenon_H3:=zenon_H5 in (zenon_all _p_T_T (fun x:_p_T_T=>(Is_true (
_p_T_equal x x))) zenon_Tx_e (fun zenon_H2=>(zenon_H3 zenon_H2))
_p_T_equal_reflexive))) zenon_H6)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_reflexive :
      forall x : abst_T, Is_true ((abst_equal x x)).
    assert (__force_use_p_T_T := _p_T_T).
    assert (__force_use__p_T_equal := _p_T_equal).
    assert (__force_use__p_T_equal_reflexive := _p_T_equal_reflexive).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_equal := abst_equal).
    apply for_zenon_equal_reflexive;
    auto.
    Qed.
    End Proof_of_equal_reflexive.
  
  Theorem equal_reflexive  (_p_T_T : Set) (_p_T_equal :
    _p_T_T -> _p_T_T -> basics.bool__t) (_p_T_equal_reflexive :
    forall x : _p_T_T, Is_true ((_p_T_equal x x))) (abst_T := _p_T_T)
    (abst_equal := equal _p_T_T _p_T_equal):
    forall x : abst_T, Is_true ((abst_equal x x)).
  apply for_zenon_abstracted_equal_reflexive;
  auto.
  Qed.
  
  (* From species value#Imp_value. *)
  (* Section for proof of theorem 'equal_symmetric'. *)
  Section Proof_of_equal_symmetric.
    Variable _p_T_T : Set.
    Variable _p_T_equal : _p_T_T -> _p_T_T -> basics.bool__t.
    Variable _p_T_equal_symmetric :
      forall x  y : _p_T_T,
        Is_true ((_p_T_equal x y)) -> Is_true ((_p_T_equal y x)).
    Let abst_T := _p_T_T.
    Let abst_equal := equal _p_T_T
    _p_T_equal.
(* File "value.fcl", line 134, characters 4-53 *)
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
let zenon_H4:=zenon_Ha in (zenon_all _p_T_T (fun x:_p_T_T=>(forall y
:_p_T_T,((Is_true (_p_T_equal x y))->(Is_true (_p_T_equal y x)))))
zenon_Tx_c (fun zenon_H8=>(zenon_all _p_T_T (fun y:_p_T_T=>((Is_true (
_p_T_equal zenon_Tx_c y))->(Is_true (_p_T_equal y zenon_Tx_c))))
zenon_Ty_j (fun zenon_H7=>(zenon_imply _ _ (fun zenon_H6=>(zenon_H6
zenon_H5)) (fun zenon_H3=>(zenon_H4 zenon_H3)) zenon_H7)) zenon_H8))
_p_T_equal_symmetric)))) zenon_Hc)) zenon_Hd)) zenon_He)) zenon_Hf))
zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_symmetric :
      forall x  y : abst_T,
        Is_true ((abst_equal x y)) -> Is_true ((abst_equal y x)).
    assert (__force_use_p_T_T := _p_T_T).
    assert (__force_use__p_T_equal := _p_T_equal).
    assert (__force_use__p_T_equal_symmetric := _p_T_equal_symmetric).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_equal := abst_equal).
    apply for_zenon_equal_symmetric;
    auto.
    Qed.
    End Proof_of_equal_symmetric.
  
  Theorem equal_symmetric  (_p_T_T : Set) (_p_T_equal :
    _p_T_T -> _p_T_T -> basics.bool__t) (_p_T_equal_symmetric :
    forall x  y : _p_T_T,
      Is_true ((_p_T_equal x y)) -> Is_true ((_p_T_equal y x)))
    (abst_T := _p_T_T) (abst_equal := equal _p_T_T _p_T_equal):
    forall x  y : abst_T,
      Is_true ((abst_equal x y)) -> Is_true ((abst_equal y x)).
  apply for_zenon_abstracted_equal_symmetric;
  auto.
  Qed.
  
  (* From species value#Imp_value. *)
  (* Section for proof of theorem 'equal_transitive'. *)
  Section Proof_of_equal_transitive.
    Variable _p_T_T : Set.
    Variable _p_T_equal : _p_T_T -> _p_T_T -> basics.bool__t.
    Variable _p_T_equal_transitive :
      forall x  y  z : _p_T_T,
        Is_true ((_p_T_equal x y)) ->
          Is_true ((_p_T_equal y z)) -> Is_true ((_p_T_equal x z)).
    Let abst_T := _p_T_T.
    Let abst_equal := equal _p_T_T
    _p_T_equal.
(* File "value.fcl", line 131, characters 4-54 *)
Theorem for_zenon_equal_transitive:(forall x:abst_T,(forall y:abst_T,(
forall z:abst_T,((Is_true (abst_equal x y))->((Is_true (abst_equal y z))
->(Is_true (abst_equal x z))))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>(forall y:abst_T,(
forall z:abst_T,((Is_true (abst_equal x y))->((Is_true (abst_equal y z))
->(Is_true (abst_equal x z))))))) (fun zenon_H24=>(zenon_ex abst_T (fun
x:abst_T=>(~(forall y:abst_T,(forall z:abst_T,((Is_true (abst_equal x y)
)->((Is_true (abst_equal y z))->(Is_true (abst_equal x z)))))))) (fun(
zenon_Tx_c:abst_T) zenon_H23=>(zenon_notallex (fun y:abst_T=>(forall z
:abst_T,((Is_true (abst_equal zenon_Tx_c y))->((Is_true (abst_equal y z)
)->(Is_true (abst_equal zenon_Tx_c z)))))) (fun zenon_H22=>(zenon_ex
abst_T (fun y:abst_T=>(~(forall z:abst_T,((Is_true (abst_equal
zenon_Tx_c y))->((Is_true (abst_equal y z))->(Is_true (abst_equal
zenon_Tx_c z))))))) (fun(zenon_Ty_d:abst_T) zenon_H21=>(zenon_notallex (
fun z:abst_T=>((Is_true (abst_equal zenon_Tx_c zenon_Ty_d))->((Is_true (
abst_equal zenon_Ty_d z))->(Is_true (abst_equal zenon_Tx_c z))))) (fun
zenon_H20=>(zenon_ex abst_T (fun z:abst_T=>(~((Is_true (abst_equal
zenon_Tx_c zenon_Ty_d))->((Is_true (abst_equal zenon_Ty_d z))->(Is_true
(abst_equal zenon_Tx_c z)))))) (fun(zenon_Tz_f:abst_T) zenon_H1f=>(
zenon_notimply _ _ (fun zenon_H1d zenon_H1e=>(zenon_notimply _ _ (fun
zenon_H1c zenon_H1b=>(let zenon_Hc:=zenon_H1d in (let zenon_H7
:=zenon_H1c in (let zenon_H6:=zenon_H1b in (let zenon_H18:=(fun
zenon_H1a=>(zenon_and _ _ (fun zenon_H16 zenon_Hd=>(zenon_Hd zenon_Hc))
zenon_H1a)) in (let zenon_H4:=(fun zenon_H19=>(zenon_subst _ (fun
zenon_Vf=>(Is_true zenon_Vf)) (_p_T_equal zenon_Ty_d zenon_Tz_f) (
_p_T_equal zenon_Tx_c zenon_Tz_f) (fun zenon_H8=>(zenon_subst _ (fun
zenon_Vg=>(~((_p_T_equal zenon_Vg zenon_Tz_f) = (_p_T_equal zenon_Tx_c
zenon_Tz_f)))) zenon_Ty_d zenon_Tx_c (fun zenon_H13=>(zenon_notand _ _ (
fun zenon_H17=>(zenon_H17 (fun zenon_H15=>(let zenon_H12:=(fun
zenon_H14=>(zenon_subst _ (fun zenon_Vh=>(zenon_Vh = zenon_Tx_c))
zenon_Tx_c zenon_Ty_d (fun zenon_H16=>(zenon_H16 zenon_H15)) zenon_H13
zenon_H14)) in (zenon_noteq _ zenon_Tx_c zenon_H12))))) (fun zenon_H11=>
(zenon_H11 (fun zenon_Hc=>(zenon_all _p_T_T (fun x:_p_T_T=>(forall y
:_p_T_T,(forall z:_p_T_T,((Is_true (_p_T_equal x y))->((Is_true (
_p_T_equal y z))->(Is_true (_p_T_equal x z))))))) zenon_Tx_c (fun
zenon_H10=>(zenon_all _p_T_T (fun y:_p_T_T=>(forall z:_p_T_T,((Is_true (
_p_T_equal zenon_Tx_c y))->((Is_true (_p_T_equal y z))->(Is_true (
_p_T_equal zenon_Tx_c z)))))) zenon_Ty_d (fun zenon_Hf=>(zenon_all
_p_T_T (fun z:_p_T_T=>((Is_true (_p_T_equal zenon_Tx_c zenon_Ty_d))->((
Is_true (_p_T_equal zenon_Ty_d z))->(Is_true (_p_T_equal zenon_Tx_c z)))
)) zenon_Tz_f (fun zenon_He=>(zenon_imply _ _ (fun zenon_Hd=>(zenon_Hd
zenon_Hc)) (fun zenon_Hb=>(zenon_imply _ _ (fun zenon_Ha=>(zenon_Ha
zenon_H7)) (fun zenon_H9=>(zenon_H6 zenon_H9)) zenon_Hb)) zenon_He))
zenon_Hf)) zenon_H10)) _p_T_equal_transitive)))) zenon_H18)) (
zenon_notnot _ (refl_equal (_p_T_equal zenon_Tx_c zenon_Tz_f)))
zenon_H8)) zenon_H6 zenon_H7)) in (zenon_noteq _ zenon_Tz_f zenon_H4))))
))) zenon_H1e)) zenon_H1f)) zenon_H20)) zenon_H21)) zenon_H22))
zenon_H23)) zenon_H24)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_transitive :
      forall x  y  z : abst_T,
        Is_true ((abst_equal x y)) ->
          Is_true ((abst_equal y z)) -> Is_true ((abst_equal x z)).
    assert (__force_use_p_T_T := _p_T_T).
    assert (__force_use__p_T_equal := _p_T_equal).
    assert (__force_use__p_T_equal_transitive := _p_T_equal_transitive).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_equal := abst_equal).
    apply for_zenon_equal_transitive;
    auto.
    Qed.
    End Proof_of_equal_transitive.
  
  Theorem equal_transitive  (_p_T_T : Set) (_p_T_equal :
    _p_T_T -> _p_T_T -> basics.bool__t) (_p_T_equal_transitive :
    forall x  y  z : _p_T_T,
      Is_true ((_p_T_equal x y)) ->
        Is_true ((_p_T_equal y z)) -> Is_true ((_p_T_equal x z)))
    (abst_T := _p_T_T) (abst_equal := equal _p_T_T _p_T_equal):
    forall x  y  z : abst_T,
      Is_true ((abst_equal x y)) ->
        Is_true ((abst_equal y z)) -> Is_true ((abst_equal x z)).
  apply for_zenon_abstracted_equal_transitive;
  auto.
  Qed.
  
  (* Fully defined 'Imp_value' species's collection generator. *)
  Definition collection_create (_p_T_T : Set) _p_T_element _p_T_equal
    _p_T_equal_reflexive _p_T_equal_symmetric _p_T_equal_transitive
    _p_T_parse _p_T_print :=
    let local_rep := _p_T_T in
    (* From species value#Imp_value. *)
    let local_consistency_rule := consistency_rule _p_T_T _p_T_equal in
    (* From species value#Imp_value. *)
    let local_element := element _p_T_T _p_T_element in
    (* From species value#Imp_value. *)
    let local_equal := equal _p_T_T _p_T_equal in
    (* From species value#Imp_value. *)
    let local_parse := parse _p_T_T _p_T_parse in
    (* From species value#Imp_value. *)
    let local_print := print _p_T_T _p_T_print in
    (* From species value#Imp_value. *)
    let local_consistency_rule_reflexive := consistency_rule_reflexive _p_T_T
      _p_T_equal _p_T_equal_reflexive in
    (* From species value#Imp_value. *)
    let local_consistency_rule_symmetric := consistency_rule_symmetric _p_T_T
      _p_T_equal _p_T_equal_symmetric in
    (* From species sets#Setoid. *)
    let local_different := sets.Setoid.different local_rep local_equal in
    (* From species value#Imp_value. *)
    let local_equal_reflexive := equal_reflexive _p_T_T _p_T_equal
      _p_T_equal_reflexive in
    (* From species value#Imp_value. *)
    let local_equal_symmetric := equal_symmetric _p_T_T _p_T_equal
      _p_T_equal_symmetric in
    (* From species value#Imp_value. *)
    let local_equal_transitive := equal_transitive _p_T_T _p_T_equal
      _p_T_equal_transitive in
    (* From species sets#Setoid. *)
    let local_same_is_not_different := sets.Setoid.same_is_not_different
      local_rep local_equal in
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
    mk_record (_p_T_T : Set) local_rep local_consistency_rule local_element
    local_equal local_parse local_print local_consistency_rule_reflexive
    local_consistency_rule_symmetric local_different local_equal_reflexive
    local_equal_symmetric local_equal_transitive local_same_is_not_different
    local_different_is_complete local_different_is_irreflexive
    local_different_is_symmetric.
  
End Imp_value.

Module Spe_int_imp_value_tol2.
  Record me_as_species : Type :=
    mk_record {
    rf_T : Set ;
    (* From species value#Spe_int_imp_value_tol2. *)
    rf_tol_is_positive :
      Is_true ((basic_type.Coll_int_value.pos
                 (basic_type.Coll_int_value.of_int 2))) ;
    (* From species value#Imp_value_tol. *)
    rf_consistency_rule : rf_T -> rf_T -> basics.bool__t ;
    (* From species value#Imp_value_tol. *)
    rf_element : rf_T ;
    (* From species value#Imp_value_tol. *)
    rf_equal : rf_T -> rf_T -> basics.bool__t ;
    (* From species value#Imp_value_tol. *)
    rf_parse : basics.string__t -> rf_T ;
    (* From species value#Imp_value_tol. *)
    rf_print : rf_T -> basics.string__t ;
    (* From species value#Imp_value_tol. *)
    rf_consistency_rule_reflexive :
      forall a : rf_T, Is_true ((rf_consistency_rule a a)) ;
    (* From species value#Imp_value_tol. *)
    rf_consistency_rule_symmetric :
      forall a  b : rf_T,
        Is_true ((rf_consistency_rule a b)) ->
          Is_true ((rf_consistency_rule b a)) ;
    (* From species sets#Setoid. *)
    rf_different : rf_T -> rf_T -> basics.bool__t ;
    (* From species value#Imp_value_tol. *)
    rf_equal_reflexive : forall x : rf_T, Is_true ((rf_equal x x)) ;
    (* From species value#Imp_value_tol. *)
    rf_equal_symmetric :
      forall x  y : rf_T,
        Is_true ((rf_equal x y)) -> Is_true ((rf_equal y x)) ;
    (* From species value#Imp_value_tol. *)
    rf_equal_transitive :
      forall x  y  z : rf_T,
        Is_true ((rf_equal x y)) ->
          Is_true ((rf_equal y z)) -> Is_true ((rf_equal x z)) ;
    (* From species sets#Setoid. *)
    rf_same_is_not_different :
      forall x  y : rf_T,
        Is_true ((rf_different x y)) <-> ~Is_true (((rf_equal x y))) ;
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
  
  
  (* From species value#Spe_int_imp_value_tol2. *)
  (* Section for proof of theorem 'tol_is_positive'. *)
  Section Proof_of_tol_is_positive.
    Section __J_1.
      (* Theorem's body. *)
      Theorem __J_1_LEMMA :
        Is_true ((basic_type.Coll_int_value.pos
                   (basic_type.Coll_int_value.of_int 2))).
      (* Proof was flagged as assumed. *)
      apply coq_builtins.magic_prove.
      Qed.
      End __J_1.
(* File "value.fcl", line 161, characters 11-74 *)
Theorem for_zenon_tol_is_positive:(Is_true (
basic_type.Coll_int_value.pos (basic_type.Coll_int_value.of_int 2))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G __J_1_LEMMA)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_tol_is_positive :
      Is_true ((basic_type.Coll_int_value.pos
                 (basic_type.Coll_int_value.of_int 2))).
    apply for_zenon_tol_is_positive;
    auto.
    Qed.
    End Proof_of_tol_is_positive.
  
  Theorem tol_is_positive :
    Is_true ((basic_type.Coll_int_value.pos
               (basic_type.Coll_int_value.of_int 2))).
  apply for_zenon_abstracted_tol_is_positive;
  auto.
  Qed.
  
  (* Fully defined 'Spe_int_imp_value_tol2' species's collection generator. *)
  Definition collection_create :=
    let local_rep := basic_type.Coll_int_value.me_as_carrier in
    (* From species value#Spe_int_imp_value_tol2. *)
    let local_tol_is_positive := tol_is_positive in
    (* From species value#Imp_value_tol. *)
    let local_consistency_rule := Imp_value_tol.consistency_rule
      basic_type.Coll_int_value.me_as_carrier basic_type.Coll_int_value.geq
      basic_type.Coll_int_value.plus ((basic_type.Coll_int_value.of_int 2))
      in
    (* From species value#Imp_value_tol. *)
    let local_element := Imp_value_tol.element
      basic_type.Coll_int_value.me_as_carrier
      basic_type.Coll_int_value.element in
    (* From species value#Imp_value_tol. *)
    let local_equal := Imp_value_tol.equal
      basic_type.Coll_int_value.me_as_carrier basic_type.Coll_int_value.equal
      in
    (* From species value#Imp_value_tol. *)
    let local_parse := Imp_value_tol.parse
      basic_type.Coll_int_value.me_as_carrier basic_type.Coll_int_value.parse
      in
    (* From species value#Imp_value_tol. *)
    let local_print := Imp_value_tol.print
      basic_type.Coll_int_value.me_as_carrier basic_type.Coll_int_value.print
      in
    (* From species value#Imp_value_tol. *)
    let local_consistency_rule_reflexive :=
      Imp_value_tol.consistency_rule_reflexive
      basic_type.Coll_int_value.me_as_carrier basic_type.Coll_int_value.geq
      basic_type.Coll_int_value.plus ((basic_type.Coll_int_value.of_int 2))
      in
    (* From species value#Imp_value_tol. *)
    let local_consistency_rule_symmetric :=
      Imp_value_tol.consistency_rule_symmetric
      basic_type.Coll_int_value.me_as_carrier local_rep
      local_consistency_rule in
    (* From species sets#Setoid. *)
    let local_different := sets.Setoid.different local_rep local_equal in
    (* From species value#Imp_value_tol. *)
    let local_equal_reflexive := Imp_value_tol.equal_reflexive
      basic_type.Coll_int_value.me_as_carrier basic_type.Coll_int_value.equal
      basic_type.Coll_int_value.equal_reflexive in
    (* From species value#Imp_value_tol. *)
    let local_equal_symmetric := Imp_value_tol.equal_symmetric
      basic_type.Coll_int_value.me_as_carrier basic_type.Coll_int_value.equal
      basic_type.Coll_int_value.equal_symmetric in
    (* From species value#Imp_value_tol. *)
    let local_equal_transitive := Imp_value_tol.equal_transitive
      basic_type.Coll_int_value.me_as_carrier basic_type.Coll_int_value.equal
      basic_type.Coll_int_value.equal_transitive in
    (* From species sets#Setoid. *)
    let local_same_is_not_different := sets.Setoid.same_is_not_different
      local_rep local_equal in
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
    mk_record local_rep local_tol_is_positive local_consistency_rule
    local_element local_equal local_parse local_print
    local_consistency_rule_reflexive local_consistency_rule_symmetric
    local_different local_equal_reflexive local_equal_symmetric
    local_equal_transitive local_same_is_not_different
    local_different_is_complete local_different_is_irreflexive
    local_different_is_symmetric.
  
End Spe_int_imp_value_tol2.

Module Coll_int_imp_value_tol.
  Let effective_collection := Spe_int_imp_value_tol2.collection_create.
  (* Carrier's structure explicitly given by "rep". *)
  Definition me_as_carrier := basic_type.Coll_int_value.me_as_carrier.
  Definition tol_is_positive :=
    effective_collection.(Spe_int_imp_value_tol2.rf_tol_is_positive).
  Definition consistency_rule :=
    effective_collection.(Spe_int_imp_value_tol2.rf_consistency_rule).
  Definition element :=
    effective_collection.(Spe_int_imp_value_tol2.rf_element).
  Definition equal := effective_collection.(Spe_int_imp_value_tol2.rf_equal).
  Definition parse := effective_collection.(Spe_int_imp_value_tol2.rf_parse).
  Definition print := effective_collection.(Spe_int_imp_value_tol2.rf_print).
  Definition consistency_rule_reflexive :=
    effective_collection.(Spe_int_imp_value_tol2.rf_consistency_rule_reflexive).
  Definition consistency_rule_symmetric :=
    effective_collection.(Spe_int_imp_value_tol2.rf_consistency_rule_symmetric).
  Definition different :=
    effective_collection.(Spe_int_imp_value_tol2.rf_different).
  Definition equal_reflexive :=
    effective_collection.(Spe_int_imp_value_tol2.rf_equal_reflexive).
  Definition equal_symmetric :=
    effective_collection.(Spe_int_imp_value_tol2.rf_equal_symmetric).
  Definition equal_transitive :=
    effective_collection.(Spe_int_imp_value_tol2.rf_equal_transitive).
  Definition same_is_not_different :=
    effective_collection.(Spe_int_imp_value_tol2.rf_same_is_not_different).
  Definition different_is_complete :=
    effective_collection.(Spe_int_imp_value_tol2.rf_different_is_complete).
  Definition different_is_irreflexive :=
    effective_collection.(Spe_int_imp_value_tol2.rf_different_is_irreflexive).
  Definition different_is_symmetric :=
    effective_collection.(Spe_int_imp_value_tol2.rf_different_is_symmetric).
  
End Coll_int_imp_value_tol.

Module Coll_int_imp_value.
  Let effective_collection := Imp_value.collection_create
    basic_type.Coll_int_value.me_as_carrier basic_type.Coll_int_value.element
    basic_type.Coll_int_value.equal basic_type.Coll_int_value.equal_reflexive
    basic_type.Coll_int_value.equal_symmetric
    basic_type.Coll_int_value.equal_transitive
    basic_type.Coll_int_value.parse basic_type.Coll_int_value.print.
  (* Carrier's structure explicitly given by "rep". *)
  Definition me_as_carrier := basic_type.Coll_int_value.me_as_carrier.
  Definition consistency_rule :=
    effective_collection.(Imp_value.rf_consistency_rule _).
  Definition element := effective_collection.(Imp_value.rf_element _).
  Definition equal := effective_collection.(Imp_value.rf_equal _).
  Definition parse := effective_collection.(Imp_value.rf_parse _).
  Definition print := effective_collection.(Imp_value.rf_print _).
  Definition consistency_rule_reflexive :=
    effective_collection.(Imp_value.rf_consistency_rule_reflexive _).
  Definition consistency_rule_symmetric :=
    effective_collection.(Imp_value.rf_consistency_rule_symmetric _).
  Definition different := effective_collection.(Imp_value.rf_different _).
  Definition equal_reflexive :=
    effective_collection.(Imp_value.rf_equal_reflexive _).
  Definition equal_symmetric :=
    effective_collection.(Imp_value.rf_equal_symmetric _).
  Definition equal_transitive :=
    effective_collection.(Imp_value.rf_equal_transitive _).
  Definition same_is_not_different :=
    effective_collection.(Imp_value.rf_same_is_not_different _).
  Definition different_is_complete :=
    effective_collection.(Imp_value.rf_different_is_complete _).
  Definition different_is_irreflexive :=
    effective_collection.(Imp_value.rf_different_is_irreflexive _).
  Definition different_is_symmetric :=
    effective_collection.(Imp_value.rf_different_is_symmetric _).
  
End Coll_int_imp_value.

Module Coll_bool_imp_value.
  Let effective_collection := Imp_value.collection_create
    basic_type.Coll_bool_value.me_as_carrier
    basic_type.Coll_bool_value.element basic_type.Coll_bool_value.equal
    basic_type.Coll_bool_value.equal_reflexive
    basic_type.Coll_bool_value.equal_symmetric
    basic_type.Coll_bool_value.equal_transitive
    basic_type.Coll_bool_value.parse basic_type.Coll_bool_value.print.
  (* Carrier's structure explicitly given by "rep". *)
  Definition me_as_carrier := basic_type.Coll_bool_value.me_as_carrier.
  Definition consistency_rule :=
    effective_collection.(Imp_value.rf_consistency_rule _).
  Definition element := effective_collection.(Imp_value.rf_element _).
  Definition equal := effective_collection.(Imp_value.rf_equal _).
  Definition parse := effective_collection.(Imp_value.rf_parse _).
  Definition print := effective_collection.(Imp_value.rf_print _).
  Definition consistency_rule_reflexive :=
    effective_collection.(Imp_value.rf_consistency_rule_reflexive _).
  Definition consistency_rule_symmetric :=
    effective_collection.(Imp_value.rf_consistency_rule_symmetric _).
  Definition different := effective_collection.(Imp_value.rf_different _).
  Definition equal_reflexive :=
    effective_collection.(Imp_value.rf_equal_reflexive _).
  Definition equal_symmetric :=
    effective_collection.(Imp_value.rf_equal_symmetric _).
  Definition equal_transitive :=
    effective_collection.(Imp_value.rf_equal_transitive _).
  Definition same_is_not_different :=
    effective_collection.(Imp_value.rf_same_is_not_different _).
  Definition different_is_complete :=
    effective_collection.(Imp_value.rf_different_is_complete _).
  Definition different_is_irreflexive :=
    effective_collection.(Imp_value.rf_different_is_irreflexive _).
  Definition different_is_symmetric :=
    effective_collection.(Imp_value.rf_different_is_symmetric _).
  
End Coll_bool_imp_value.

