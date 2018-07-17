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
Require valid_meas.
Require gen_value.
Require basic_type.
Require pair.
Module Sp_value_with_valid.
  
End Sp_value_with_valid.

Module Imp_value_with_valid.
  Record me_as_species (T_T : Set) (V_T : Set) (_p_T_equal : T_T ->
                                                               T_T ->
                                                                 basics.bool__t)
    (_p_V_equal : V_T -> V_T -> basics.bool__t) : Type :=
    mk_record {
    rf_T : Set ;
    (* From species pair#Imp_pair. *)
    rf_constr : T_T -> V_T -> rf_T ;
    (* From species pair#Imp_pair. *)
    rf_equal : rf_T -> rf_T -> basics.bool__t ;
    (* From species basics#Basic_object. *)
    rf_parse : basics.string__t -> rf_T ;
    (* From species pair#Imp_pair. *)
    rf_prj_a : rf_T -> T_T ;
    (* From species pair#Imp_pair. *)
    rf_prj_b : rf_T -> V_T ;
    (* From species pair#Imp_pair. *)
    rf_element : rf_T ;
    (* From species value_with_valid#Imp_value_with_valid. *)
    rf_parse2 : basics.string__t -> basics.string__t -> rf_T ;
    (* From species sets#Setoid. *)
    rf_different : rf_T -> rf_T -> basics.bool__t ;
    (* From species pair#Imp_pair. *)
    rf_prj_a_is_first_of_pair :
      forall n1 : T_T,
        forall n2 : V_T,
          Is_true ((_p_T_equal (rf_prj_a (rf_constr n1 n2)) n1)) ;
    (* From species value_with_valid#Imp_value_with_valid. *)
    rf_consistency_rule : rf_T -> rf_T -> basics.bool__t ;
    (* From species pair#Imp_pair. *)
    rf_def_equal :
      forall p1  p2 : rf_T,
        Is_true ((rf_equal p1 p2)) <->
          (Is_true ((_p_T_equal (rf_prj_a p1) (rf_prj_a p2))) /\
             Is_true ((_p_V_equal (rf_prj_b p1) (rf_prj_b p2)))) ;
    (* From species value_with_valid#Imp_value_with_valid. *)
    rf_print : rf_T -> basics.string__t ;
    (* From species pair#Imp_pair. *)
    rf_prj_b_is_snd_of_pair :
      forall n1 : T_T,
        forall n2 : V_T,
          Is_true ((_p_V_equal (rf_prj_b (rf_constr n1 n2)) n2)) ;
    (* From species pair#Imp_pair. *)
    rf_unicite_1 :
      forall a : rf_T,
        Is_true ((rf_equal (rf_constr (rf_prj_a a) (rf_prj_b a)) a)) ;
    (* From species pair#Imp_pair. *)
    rf_unicite_2 :
      forall a : rf_T,
        Is_true ((rf_equal a (rf_constr (rf_prj_a a) (rf_prj_b a)))) ;
    (* From species sets#Setoid. *)
    rf_same_is_not_different :
      forall x  y : rf_T,
        Is_true ((rf_different x y)) <-> ~Is_true (((rf_equal x y))) ;
    (* From species value_with_valid#Imp_value_with_valid. *)
    rf_consistency_rule_reflexive :
      forall a : rf_T, Is_true ((rf_consistency_rule a a)) ;
    (* From species value_with_valid#Imp_value_with_valid. *)
    rf_consistency_rule_symmetric :
      forall a  b : rf_T,
        Is_true ((rf_consistency_rule a b)) ->
          Is_true ((rf_consistency_rule b a)) ;
    (* From species pair#Imp_pair. *)
    rf_equal_transitive :
      forall x  y  z : rf_T,
        Is_true ((rf_equal x y)) ->
          Is_true ((rf_equal y z)) -> Is_true ((rf_equal x z)) ;
    (* From species pair#Imp_pair. *)
    rf_def_equal1 :
      forall n1  n3 : T_T,
        forall n2  n4 : V_T,
          Is_true ((rf_equal (rf_constr n1 n2) (rf_constr n3 n4))) <->
            (Is_true ((_p_T_equal n1 n3)) /\ Is_true ((_p_V_equal n2 n4))) ;
    (* From species pair#Imp_pair. *)
    rf_equal_reflexive : forall x : rf_T, Is_true ((rf_equal x x)) ;
    (* From species pair#Imp_pair. *)
    rf_equal_reflexive2 :
      forall n1 : T_T,
        forall n2 : V_T,
          Is_true ((rf_equal (rf_constr n1 n2) (rf_constr n1 n2))) ;
    (* From species pair#Imp_pair. *)
    rf_equal_symmetric2 :
      forall n1  n3 : T_T,
        forall n2  n4 : V_T,
          Is_true ((rf_equal (rf_constr n1 n2) (rf_constr n3 n4))) ->
            Is_true ((rf_equal (rf_constr n3 n4) (rf_constr n1 n2))) ;
    (* From species pair#Imp_pair. *)
    rf_equal_transitive2 :
      forall n1  n3  n5 : T_T,
        forall n2  n4  n6 : V_T,
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
  
  Definition parse2 (_p_T_T : Set) (_p_V_T : Set) (_p_T_parse :
    basics.string__t -> _p_T_T) (_p_V_parse : basics.string__t -> _p_V_T)
    (abst_T : Set) (abst_constr : _p_T_T -> _p_V_T -> abst_T)
    (x : basics.string__t) (y : basics.string__t) : abst_T :=
    (abst_constr (_p_T_parse x) (_p_V_parse y)).
  Definition consistency_rule (_p_T_T : Set) (_p_V_T : Set) (_p_T_equal :
    _p_T_T -> _p_T_T -> basics.bool__t) (_p_V_equal :
    _p_V_T -> _p_V_T -> basics.bool__t) (_p_V_valid : _p_V_T) (abst_T : Set)
    (abst_prj_a : abst_T -> _p_T_T) (abst_prj_b : abst_T -> _p_V_T)
    (x : abst_T) (y : abst_T) : basics.bool__t :=
    (if (_p_V_equal (abst_prj_b x) _p_V_valid)
      then (if (_p_V_equal (abst_prj_b y) _p_V_valid)
             then (_p_T_equal (abst_prj_a x) (abst_prj_a y)) else false)
      else (if (_p_V_equal (abst_prj_b y) _p_V_valid) then false else true)).
  Definition print (_p_T_T : Set) (_p_V_T : Set) (_p_T_print :
    _p_T_T -> basics.string__t) (_p_V_print : _p_V_T -> basics.string__t)
    (abst_T : Set) (abst_prj_a : abst_T -> _p_T_T)
    (abst_prj_b : abst_T -> _p_V_T) (x : abst_T) : basics.string__t :=
    let a : basics.string__t :=
      "( "%string
    in
    let b : basics.string__t :=
      (_p_T_print (abst_prj_a x))
    in
    let c : basics.string__t :=
      ", "%string
    in
    let d : basics.string__t :=
      (_p_V_print (abst_prj_b x))
    in
    let e : basics.string__t :=
      ")"%string
    in
    ((basics._hat_ a (basics._hat_ b (basics._hat_ c (basics._hat_ d e))))).
  
  (* From species value_with_valid#Imp_value_with_valid. *)
  (* Section for proof of theorem 'consistency_rule_reflexive'. *)
  Section Proof_of_consistency_rule_reflexive.
    Variable _p_T_T : Set.
    Variable _p_V_T : Set.
    Variable _p_T_equal : _p_T_T -> _p_T_T -> basics.bool__t.
    Variable _p_T_equal_reflexive :
      forall x : _p_T_T, Is_true ((_p_T_equal x x)).
    Variable _p_V_equal : _p_V_T -> _p_V_T -> basics.bool__t.
    Variable _p_V_valid : _p_V_T.
    Variable abst_T : Set.
    Variable abst_prj_a : abst_T -> _p_T_T.
    Variable abst_prj_b : abst_T -> _p_V_T.
    Let abst_consistency_rule := consistency_rule _p_T_T _p_V_T _p_T_equal
    _p_V_equal _p_V_valid abst_T abst_prj_a
    abst_prj_b.
(* File "value_with_valid.fcl", line 65, characters 4-64 *)
Theorem for_zenon_consistency_rule_reflexive:(forall a:abst_T,(Is_true (
abst_consistency_rule a a))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun a:abst_T=>(Is_true (
abst_consistency_rule a a))) (fun zenon_Hd=>(zenon_ex abst_T (fun a
:abst_T=>(~(Is_true (abst_consistency_rule a a)))) (fun(zenon_Ta_c
:abst_T) zenon_Hc=>(let zenon_Hb:=zenon_Hc in (zenon_focal_ite_bool_n (
_p_V_equal (abst_prj_b zenon_Ta_c) _p_V_valid) (if (_p_V_equal (
abst_prj_b zenon_Ta_c) _p_V_valid) then (_p_T_equal (abst_prj_a
zenon_Ta_c) (abst_prj_a zenon_Ta_c)) else false) (if (_p_V_equal (
abst_prj_b zenon_Ta_c) _p_V_valid) then false else true) (fun zenon_H5
zenon_H8=>(zenon_focal_ite_bool_n (_p_V_equal (abst_prj_b zenon_Ta_c)
_p_V_valid) (_p_T_equal (abst_prj_a zenon_Ta_c) (abst_prj_a zenon_Ta_c))
 false (fun zenon_H5 zenon_H4=>(zenon_all _p_T_T (fun x:_p_T_T=>(
Is_true (_p_T_equal x x))) (abst_prj_a zenon_Ta_c) (fun zenon_H3=>(
zenon_H4 zenon_H3)) _p_T_equal_reflexive)) (fun zenon_H6 zenon_H7=>(
zenon_H6 zenon_H5)) zenon_H8)) (fun zenon_H6 zenon_Ha=>(
zenon_focal_ite_bool_n (_p_V_equal (abst_prj_b zenon_Ta_c) _p_V_valid)
false true (fun zenon_H5 zenon_H7=>(zenon_H6 zenon_H5)) (fun zenon_H6
zenon_H9=>(zenon_focal_nottrue zenon_H9)) zenon_Ha)) zenon_Hb)))
zenon_Hd)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_consistency_rule_reflexive :
      forall a : abst_T, Is_true ((abst_consistency_rule a a)).
    assert (__force_use_p_T_T := _p_T_T).
    assert (__force_use_p_V_T := _p_V_T).
    assert (__force_use__p_T_equal := _p_T_equal).
    assert (__force_use__p_T_equal_reflexive := _p_T_equal_reflexive).
    assert (__force_use__p_V_equal := _p_V_equal).
    assert (__force_use__p_V_valid := _p_V_valid).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_prj_a := abst_prj_a).
    assert (__force_use_abst_prj_b := abst_prj_b).
    assert (__force_use_abst_consistency_rule := abst_consistency_rule).
    apply for_zenon_consistency_rule_reflexive;
    auto.
    Qed.
    End Proof_of_consistency_rule_reflexive.
  
  Theorem consistency_rule_reflexive  (_p_T_T : Set) (_p_V_T : Set)
    (_p_T_equal : _p_T_T -> _p_T_T -> basics.bool__t) (_p_T_equal_reflexive :
    forall x : _p_T_T, Is_true ((_p_T_equal x x))) (_p_V_equal :
    _p_V_T -> _p_V_T -> basics.bool__t) (_p_V_valid : _p_V_T) (abst_T : Set)
    (abst_prj_a : abst_T -> _p_T_T) (abst_prj_b : abst_T -> _p_V_T)
    (abst_consistency_rule := consistency_rule _p_T_T _p_V_T _p_T_equal
    _p_V_equal _p_V_valid abst_T abst_prj_a abst_prj_b):
    forall a : abst_T, Is_true ((abst_consistency_rule a a)).
  apply for_zenon_abstracted_consistency_rule_reflexive;
  auto.
  Qed.
  
  (* From species value_with_valid#Imp_value_with_valid. *)
  (* Section for proof of theorem 'consistency_rule_symmetric'. *)
  Section Proof_of_consistency_rule_symmetric.
    Variable _p_T_T : Set.
    Variable _p_V_T : Set.
    Variable _p_T_equal : _p_T_T -> _p_T_T -> basics.bool__t.
    Variable _p_T_equal_symmetric :
      forall x  y : _p_T_T,
        Is_true ((_p_T_equal x y)) -> Is_true ((_p_T_equal y x)).
    Variable _p_V_equal : _p_V_T -> _p_V_T -> basics.bool__t.
    Variable _p_V_valid : _p_V_T.
    Variable abst_T : Set.
    Variable abst_prj_a : abst_T -> _p_T_T.
    Variable abst_prj_b : abst_T -> _p_V_T.
    Let abst_consistency_rule := consistency_rule _p_T_T _p_V_T _p_T_equal
    _p_V_equal _p_V_valid abst_T abst_prj_a
    abst_prj_b.
(* File "value_with_valid.fcl", line 62, characters 4-64 *)
Theorem for_zenon_consistency_rule_symmetric:(forall a:abst_T,(forall b
:abst_T,((Is_true (abst_consistency_rule a b))->(Is_true (
abst_consistency_rule b a))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun a:abst_T=>(forall b:abst_T,((
Is_true (abst_consistency_rule a b))->(Is_true (abst_consistency_rule b
a))))) (fun zenon_H1d=>(zenon_ex abst_T (fun a:abst_T=>(~(forall b
:abst_T,((Is_true (abst_consistency_rule a b))->(Is_true (
abst_consistency_rule b a)))))) (fun(zenon_Ta_c:abst_T) zenon_H1c=>(
zenon_notallex (fun b:abst_T=>((Is_true (abst_consistency_rule
zenon_Ta_c b))->(Is_true (abst_consistency_rule b zenon_Ta_c)))) (fun
zenon_H1b=>(zenon_ex abst_T (fun b:abst_T=>(~((Is_true (
abst_consistency_rule zenon_Ta_c b))->(Is_true (abst_consistency_rule b
zenon_Ta_c))))) (fun(zenon_Tb_d:abst_T) zenon_H1a=>(zenon_notimply _ _ (
fun zenon_H19 zenon_H18=>(let zenon_H11:=zenon_H19 in (let zenon_H17
:=zenon_H18 in (zenon_focal_ite_bool_n (_p_V_equal (abst_prj_b
zenon_Tb_d) _p_V_valid) (if (_p_V_equal (abst_prj_b zenon_Ta_c)
_p_V_valid) then (_p_T_equal (abst_prj_a zenon_Tb_d) (abst_prj_a
zenon_Ta_c)) else false) (if (_p_V_equal (abst_prj_b zenon_Ta_c)
_p_V_valid) then false else true) (fun zenon_Ha zenon_H14=>(
zenon_focal_ite_bool_n (_p_V_equal (abst_prj_b zenon_Ta_c) _p_V_valid) (
_p_T_equal (abst_prj_a zenon_Tb_d) (abst_prj_a zenon_Ta_c)) false (fun
zenon_He zenon_H5=>(zenon_focal_ite_bool (_p_V_equal (abst_prj_b
zenon_Ta_c) _p_V_valid) (if (_p_V_equal (abst_prj_b zenon_Tb_d)
_p_V_valid) then (_p_T_equal (abst_prj_a zenon_Ta_c) (abst_prj_a
zenon_Tb_d)) else false) (if (_p_V_equal (abst_prj_b zenon_Tb_d)
_p_V_valid) then false else true) (fun zenon_He zenon_Hd=>(
zenon_focal_ite_bool (_p_V_equal (abst_prj_b zenon_Tb_d) _p_V_valid) (
_p_T_equal (abst_prj_a zenon_Ta_c) (abst_prj_a zenon_Tb_d)) false (fun
zenon_Ha zenon_H6=>(zenon_all _p_T_T (fun x:_p_T_T=>(forall y:_p_T_T,((
Is_true (_p_T_equal x y))->(Is_true (_p_T_equal y x))))) (abst_prj_a
zenon_Ta_c) (fun zenon_H9=>(zenon_all _p_T_T (fun y:_p_T_T=>((Is_true (
_p_T_equal (abst_prj_a zenon_Ta_c) y))->(Is_true (_p_T_equal y (
abst_prj_a zenon_Ta_c))))) (abst_prj_a zenon_Tb_d) (fun zenon_H8=>(
zenon_imply _ _ (fun zenon_H7=>(zenon_H7 zenon_H6)) (fun zenon_H4=>(
zenon_H5 zenon_H4)) zenon_H8)) zenon_H9)) _p_T_equal_symmetric)) (fun
zenon_Hb zenon_Hc=>(zenon_Hb zenon_Ha)) zenon_Hd)) (fun zenon_Hf
zenon_H10=>(zenon_Hf zenon_He)) zenon_H11)) (fun zenon_Hf zenon_H12=>(
zenon_focal_ite_bool (_p_V_equal (abst_prj_b zenon_Ta_c) _p_V_valid) (
if (_p_V_equal (abst_prj_b zenon_Tb_d) _p_V_valid) then (_p_T_equal (
abst_prj_a zenon_Ta_c) (abst_prj_a zenon_Tb_d)) else false) (if (
_p_V_equal (abst_prj_b zenon_Tb_d) _p_V_valid) then false else true) (
fun zenon_He zenon_Hd=>(zenon_Hf zenon_He)) (fun zenon_Hf zenon_H10=>(
zenon_focal_ite_bool (_p_V_equal (abst_prj_b zenon_Tb_d) _p_V_valid)
false true (fun zenon_Ha zenon_Hc=>(zenon_H12 zenon_Hc)) (fun zenon_Hb
zenon_H13=>(zenon_Hb zenon_Ha)) zenon_H10)) zenon_H11)) zenon_H14)) (
fun zenon_Hb zenon_H16=>(zenon_focal_ite_bool_n (_p_V_equal (abst_prj_b
zenon_Ta_c) _p_V_valid) false true (fun zenon_He zenon_H12=>(
zenon_focal_ite_bool (_p_V_equal (abst_prj_b zenon_Ta_c) _p_V_valid) (
if (_p_V_equal (abst_prj_b zenon_Tb_d) _p_V_valid) then (_p_T_equal (
abst_prj_a zenon_Ta_c) (abst_prj_a zenon_Tb_d)) else false) (if (
_p_V_equal (abst_prj_b zenon_Tb_d) _p_V_valid) then false else true) (
fun zenon_He zenon_Hd=>(zenon_focal_ite_bool (_p_V_equal (abst_prj_b
zenon_Tb_d) _p_V_valid) (_p_T_equal (abst_prj_a zenon_Ta_c) (abst_prj_a
zenon_Tb_d)) false (fun zenon_Ha zenon_H6=>(zenon_Hb zenon_Ha)) (fun
zenon_Hb zenon_Hc=>(zenon_H12 zenon_Hc)) zenon_Hd)) (fun zenon_Hf
zenon_H10=>(zenon_Hf zenon_He)) zenon_H11)) (fun zenon_Hf zenon_H15=>(
zenon_focal_nottrue zenon_H15)) zenon_H16)) zenon_H17)))) zenon_H1a))
zenon_H1b)) zenon_H1c)) zenon_H1d)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_consistency_rule_symmetric :
      forall a  b : abst_T,
        Is_true ((abst_consistency_rule a b)) ->
          Is_true ((abst_consistency_rule b a)).
    assert (__force_use_p_T_T := _p_T_T).
    assert (__force_use_p_V_T := _p_V_T).
    assert (__force_use__p_T_equal := _p_T_equal).
    assert (__force_use__p_T_equal_symmetric := _p_T_equal_symmetric).
    assert (__force_use__p_V_equal := _p_V_equal).
    assert (__force_use__p_V_valid := _p_V_valid).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_prj_a := abst_prj_a).
    assert (__force_use_abst_prj_b := abst_prj_b).
    assert (__force_use_abst_consistency_rule := abst_consistency_rule).
    apply for_zenon_consistency_rule_symmetric;
    auto.
    Qed.
    End Proof_of_consistency_rule_symmetric.
  
  Theorem consistency_rule_symmetric  (_p_T_T : Set) (_p_V_T : Set)
    (_p_T_equal : _p_T_T -> _p_T_T -> basics.bool__t) (_p_T_equal_symmetric :
    forall x  y : _p_T_T,
      Is_true ((_p_T_equal x y)) -> Is_true ((_p_T_equal y x)))
    (_p_V_equal : _p_V_T -> _p_V_T -> basics.bool__t) (_p_V_valid : _p_V_T)
    (abst_T : Set) (abst_prj_a : abst_T -> _p_T_T)
    (abst_prj_b : abst_T -> _p_V_T) (abst_consistency_rule :=
    consistency_rule _p_T_T _p_V_T _p_T_equal _p_V_equal _p_V_valid abst_T
    abst_prj_a abst_prj_b):
    forall a  b : abst_T,
      Is_true ((abst_consistency_rule a b)) ->
        Is_true ((abst_consistency_rule b a)).
  apply for_zenon_abstracted_consistency_rule_symmetric;
  auto.
  Qed.
  
  (* Fully defined 'Imp_value_with_valid' species's collection generator. *)
  Definition collection_create (_p_T_T : Set) (_p_V_T : Set) _p_T_element
    _p_T_equal _p_T_equal_reflexive _p_T_equal_symmetric
    _p_T_equal_transitive _p_T_parse _p_T_print _p_V_element _p_V_equal
    _p_V_valid _p_V_equal_reflexive _p_V_equal_symmetric
    _p_V_equal_transitive _p_V_parse _p_V_print :=
    let local_rep := (Datatypes.prod _p_T_T _p_V_T) in
    (* From species pair#Imp_pair. *)
    let local_constr := pair.Imp_pair.constr _p_T_T _p_V_T in
    (* From species pair#Imp_pair. *)
    let local_equal := pair.Imp_pair.equal _p_T_T _p_V_T _p_T_equal
      _p_V_equal in
    (* From species basics#Basic_object. *)
    let local_parse := basics.Basic_object.parse local_rep in
    (* From species pair#Imp_pair. *)
    let local_prj_a := pair.Imp_pair.prj_a _p_T_T _p_V_T in
    (* From species pair#Imp_pair. *)
    let local_prj_b := pair.Imp_pair.prj_b _p_T_T _p_V_T in
    (* From species pair#Imp_pair. *)
    let local_element := pair.Imp_pair.element _p_T_T _p_V_T _p_T_element
      _p_V_element local_rep local_constr in
    (* From species value_with_valid#Imp_value_with_valid. *)
    let local_parse2 := parse2 _p_T_T _p_V_T _p_T_parse _p_V_parse local_rep
      local_constr in
    (* From species sets#Setoid. *)
    let local_different := sets.Setoid.different local_rep local_equal in
    (* From species pair#Imp_pair. *)
    let local_prj_a_is_first_of_pair := pair.Imp_pair.prj_a_is_first_of_pair
      _p_T_T _p_V_T _p_T_equal local_rep local_constr local_prj_a in
    (* From species value_with_valid#Imp_value_with_valid. *)
    let local_consistency_rule := consistency_rule _p_T_T _p_V_T _p_T_equal
      _p_V_equal _p_V_valid local_rep local_prj_a local_prj_b in
    (* From species pair#Imp_pair. *)
    let local_def_equal := pair.Imp_pair.def_equal _p_T_T _p_V_T _p_T_equal
      _p_V_equal local_rep local_equal local_prj_a local_prj_b in
    (* From species value_with_valid#Imp_value_with_valid. *)
    let local_print := print _p_T_T _p_V_T _p_T_print _p_V_print local_rep
      local_prj_a local_prj_b in
    (* From species pair#Imp_pair. *)
    let local_prj_b_is_snd_of_pair := pair.Imp_pair.prj_b_is_snd_of_pair
      _p_T_T _p_V_T _p_V_equal local_rep local_constr local_prj_b in
    (* From species pair#Imp_pair. *)
    let local_unicite_1 := pair.Imp_pair.unicite_1 _p_T_T _p_V_T local_rep
      local_constr local_equal local_prj_a local_prj_b in
    (* From species pair#Imp_pair. *)
    let local_unicite_2 := pair.Imp_pair.unicite_2 _p_T_T _p_V_T local_rep
      local_constr local_equal local_prj_a local_prj_b in
    (* From species sets#Setoid. *)
    let local_same_is_not_different := sets.Setoid.same_is_not_different
      local_rep local_equal in
    (* From species value_with_valid#Imp_value_with_valid. *)
    let local_consistency_rule_reflexive := consistency_rule_reflexive _p_T_T
      _p_V_T _p_T_equal _p_T_equal_reflexive _p_V_equal _p_V_valid local_rep
      local_prj_a local_prj_b in
    (* From species value_with_valid#Imp_value_with_valid. *)
    let local_consistency_rule_symmetric := consistency_rule_symmetric _p_T_T
      _p_V_T _p_T_equal _p_T_equal_symmetric _p_V_equal _p_V_valid local_rep
      local_prj_a local_prj_b in
    (* From species pair#Imp_pair. *)
    let local_equal_transitive := pair.Imp_pair.equal_transitive _p_T_T
      _p_V_T _p_T_equal _p_T_equal_transitive _p_V_equal
      _p_V_equal_transitive local_rep local_equal local_prj_a local_prj_b
      local_def_equal in
    (* From species pair#Imp_pair. *)
    let local_def_equal1 := pair.Imp_pair.def_equal1 _p_T_T _p_V_T _p_T_equal
      _p_T_equal_symmetric _p_T_equal_transitive _p_V_equal
      _p_V_equal_symmetric _p_V_equal_transitive local_rep local_constr
      local_equal local_prj_a local_prj_b local_prj_a_is_first_of_pair
      local_def_equal local_prj_b_is_snd_of_pair in
    (* From species pair#Imp_pair. *)
    let local_equal_reflexive := pair.Imp_pair.equal_reflexive _p_T_T _p_V_T
      local_rep local_constr local_equal local_prj_a local_prj_b
      local_unicite_1 local_unicite_2 local_equal_transitive in
    (* From species pair#Imp_pair. *)
    let local_equal_reflexive2 := pair.Imp_pair.equal_reflexive2 _p_T_T
      _p_V_T _p_T_equal _p_T_equal_reflexive _p_V_equal _p_V_equal_reflexive
      local_rep local_constr local_equal local_def_equal1 in
    (* From species pair#Imp_pair. *)
    let local_equal_symmetric2 := pair.Imp_pair.equal_symmetric2 _p_T_T
      _p_V_T _p_T_equal _p_T_equal_symmetric _p_V_equal _p_V_equal_symmetric
      local_rep local_constr local_equal local_def_equal1 in
    (* From species pair#Imp_pair. *)
    let local_equal_transitive2 := pair.Imp_pair.equal_transitive2 _p_T_T
      _p_V_T _p_T_equal _p_T_equal_transitive _p_V_equal
      _p_V_equal_transitive local_rep local_constr local_equal
      local_def_equal1 in
    (* From species sets#Setoid. *)
    let local_different_is_irreflexive :=
      sets.Setoid.different_is_irreflexive local_rep local_equal
      local_different local_equal_reflexive local_same_is_not_different in
    (* From species pair#Imp_pair. *)
    let local_equal_symmetric := pair.Imp_pair.equal_symmetric _p_T_T _p_V_T
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
    mk_record (_p_T_T : Set) (_p_V_T : Set) _p_T_equal _p_V_equal local_rep
    local_constr local_equal local_parse local_prj_a local_prj_b
    local_element local_parse2 local_different local_prj_a_is_first_of_pair
    local_consistency_rule local_def_equal local_print
    local_prj_b_is_snd_of_pair local_unicite_1 local_unicite_2
    local_same_is_not_different local_consistency_rule_reflexive
    local_consistency_rule_symmetric local_equal_transitive local_def_equal1
    local_equal_reflexive local_equal_reflexive2 local_equal_symmetric2
    local_equal_transitive2 local_different_is_irreflexive
    local_equal_symmetric local_different_is_complete
    local_different_is_symmetric.
  
End Imp_value_with_valid.

Module Coll_int_value_with_valid.
  Let effective_collection := Imp_value_with_valid.collection_create
    basic_type.Coll_int_value.me_as_carrier
    valid_meas.Coll_valid_meas.me_as_carrier
    basic_type.Coll_int_value.element basic_type.Coll_int_value.equal
    basic_type.Coll_int_value.equal_reflexive
    basic_type.Coll_int_value.equal_symmetric
    basic_type.Coll_int_value.equal_transitive
    basic_type.Coll_int_value.parse basic_type.Coll_int_value.print
    valid_meas.Coll_valid_meas.element valid_meas.Coll_valid_meas.equal
    valid_meas.Coll_valid_meas.valid
    valid_meas.Coll_valid_meas.equal_reflexive
    valid_meas.Coll_valid_meas.equal_symmetric
    valid_meas.Coll_valid_meas.equal_transitive
    valid_meas.Coll_valid_meas.parse valid_meas.Coll_valid_meas.print.
  (* Carrier's structure explicitly given by "rep". *)
  Definition me_as_carrier :=
    (Datatypes.prod basic_type.Coll_int_value.me_as_carrier
      valid_meas.Coll_valid_meas.me_as_carrier).
  Definition constr :=
    effective_collection.(Imp_value_with_valid.rf_constr _ _ _ _).
  Definition equal :=
    effective_collection.(Imp_value_with_valid.rf_equal _ _ _ _).
  Definition parse :=
    effective_collection.(Imp_value_with_valid.rf_parse _ _ _ _).
  Definition prj_a :=
    effective_collection.(Imp_value_with_valid.rf_prj_a _ _ _ _).
  Definition prj_b :=
    effective_collection.(Imp_value_with_valid.rf_prj_b _ _ _ _).
  Definition element :=
    effective_collection.(Imp_value_with_valid.rf_element _ _ _ _).
  Definition parse2 :=
    effective_collection.(Imp_value_with_valid.rf_parse2 _ _ _ _).
  Definition different :=
    effective_collection.(Imp_value_with_valid.rf_different _ _ _ _).
  Definition prj_a_is_first_of_pair :=
    effective_collection.(Imp_value_with_valid.rf_prj_a_is_first_of_pair _ _
                          _ _).
  Definition consistency_rule :=
    effective_collection.(Imp_value_with_valid.rf_consistency_rule _ _ _ _).
  Definition def_equal :=
    effective_collection.(Imp_value_with_valid.rf_def_equal _ _ _ _).
  Definition print :=
    effective_collection.(Imp_value_with_valid.rf_print _ _ _ _).
  Definition prj_b_is_snd_of_pair :=
    effective_collection.(Imp_value_with_valid.rf_prj_b_is_snd_of_pair _ _ _
                          _).
  Definition unicite_1 :=
    effective_collection.(Imp_value_with_valid.rf_unicite_1 _ _ _ _).
  Definition unicite_2 :=
    effective_collection.(Imp_value_with_valid.rf_unicite_2 _ _ _ _).
  Definition same_is_not_different :=
    effective_collection.(Imp_value_with_valid.rf_same_is_not_different _ _ _
                          _).
  Definition consistency_rule_reflexive :=
    effective_collection.(Imp_value_with_valid.rf_consistency_rule_reflexive
                          _ _ _ _).
  Definition consistency_rule_symmetric :=
    effective_collection.(Imp_value_with_valid.rf_consistency_rule_symmetric
                          _ _ _ _).
  Definition equal_transitive :=
    effective_collection.(Imp_value_with_valid.rf_equal_transitive _ _ _ _).
  Definition def_equal1 :=
    effective_collection.(Imp_value_with_valid.rf_def_equal1 _ _ _ _).
  Definition equal_reflexive :=
    effective_collection.(Imp_value_with_valid.rf_equal_reflexive _ _ _ _).
  Definition equal_reflexive2 :=
    effective_collection.(Imp_value_with_valid.rf_equal_reflexive2 _ _ _ _).
  Definition equal_symmetric2 :=
    effective_collection.(Imp_value_with_valid.rf_equal_symmetric2 _ _ _ _).
  Definition equal_transitive2 :=
    effective_collection.(Imp_value_with_valid.rf_equal_transitive2 _ _ _ _).
  Definition different_is_irreflexive :=
    effective_collection.(Imp_value_with_valid.rf_different_is_irreflexive _
                          _ _ _).
  Definition equal_symmetric :=
    effective_collection.(Imp_value_with_valid.rf_equal_symmetric _ _ _ _).
  Definition different_is_complete :=
    effective_collection.(Imp_value_with_valid.rf_different_is_complete _ _ _
                          _).
  Definition different_is_symmetric :=
    effective_collection.(Imp_value_with_valid.rf_different_is_symmetric _ _
                          _ _).
  
End Coll_int_value_with_valid.
