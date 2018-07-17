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
Module Gen_basic_type.
  
End Gen_basic_type.

Module Gen_basic_type_tol.
  
End Gen_basic_type_tol.

Module Int_value.
  Record me_as_species : Type :=
    mk_record {
    rf_T : Set ;
    (* From species basic_type#Int_value. *)
    rf_element : rf_T ;
    (* From species basic_type#Int_value. *)
    rf_equal : rf_T -> rf_T -> basics.bool__t ;
    (* From species basic_type#Int_value. *)
    rf_geq : rf_T -> rf_T -> basics.bool__t ;
    (* From species basic_type#Int_value. *)
    rf_of_int : basics.int__t -> rf_T ;
    (* From species basic_type#Int_value. *)
    rf_parse : basics.string__t -> rf_T ;
    (* From species basic_type#Int_value. *)
    rf_plus : rf_T -> rf_T -> rf_T ;
    (* From species basic_type#Int_value. *)
    rf_pos : rf_T -> basics.bool__t ;
    (* From species basic_type#Int_value. *)
    rf_print : rf_T -> basics.string__t ;
    (* From species sets#Setoid. *)
    rf_different : rf_T -> rf_T -> basics.bool__t ;
    (* From species basic_type#Int_value. *)
    rf_equal_reflexive : forall x : rf_T, Is_true ((rf_equal x x)) ;
    (* From species basic_type#Int_value. *)
    rf_equal_symmetric :
      forall x  y : rf_T,
        Is_true ((rf_equal x y)) -> Is_true ((rf_equal y x)) ;
    (* From species basic_type#Int_value. *)
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
  
  Definition element (abst_T := basics.int__t) : abst_T := 1.
  Definition equal (abst_T : Set) (x : abst_T) (y : abst_T) :
    basics.bool__t := ((basics.syntactic_equal _) x y).
  Definition geq (abst_T := basics.int__t) (n1 : abst_T) (n2 : abst_T) :
    basics.bool__t := (basics._gt__equal_ n1 n2).
  Definition of_int (abst_T := basics.int__t) (n : basics.int__t) : abst_T :=
    n.
  Definition parse (abst_T := basics.int__t) (x : basics.string__t) :
    abst_T := (basics.int_of_string x).
  Definition plus (abst_T := basics.int__t) (n1 : abst_T) (n2 : abst_T) :
    abst_T := (basics._plus_ n1 n2).
  Definition pos (abst_T := basics.int__t) (n : abst_T) : basics.bool__t :=
    (basics._gt_ n 0).
  Definition print (abst_T := basics.int__t) (x : abst_T) :
    basics.string__t := (basics.string_of_int x).
  
  (* From species basic_type#Int_value. *)
  (* Section for proof of theorem 'equal_reflexive'. *)
  Section Proof_of_equal_reflexive.
    Variable abst_T : Set.
    Let abst_equal := equal
    abst_T.
(* File "basic_type.fcl", line 62, characters 2-49 *)
Theorem for_zenon_equal_reflexive:(forall x:abst_T,(Is_true (abst_equal
x x))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>(Is_true (
abst_equal x x))) (fun zenon_H6=>(zenon_ex abst_T (fun x:abst_T=>(~(
Is_true (abst_equal x x)))) (fun(zenon_Tx_c:abst_T) zenon_H5=>(let
zenon_H4:=zenon_H5 in (coq_builtins.zenon_not_syntactic_equal _
zenon_Tx_c zenon_Tx_c (fun zenon_H3=>(zenon_noteq _ zenon_Tx_c zenon_H3)
) zenon_H4))) zenon_H6)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_reflexive :
      forall x : abst_T, Is_true ((abst_equal x x)).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_equal := abst_equal).
    apply for_zenon_equal_reflexive;
    auto.
    Qed.
    End Proof_of_equal_reflexive.
  
  Theorem equal_reflexive  (abst_T : Set) (abst_equal := equal abst_T):
    forall x : abst_T, Is_true ((abst_equal x x)).
  apply for_zenon_abstracted_equal_reflexive;
  auto.
  Qed.
  
  (* From species basic_type#Int_value. *)
  (* Section for proof of theorem 'equal_symmetric'. *)
  Section Proof_of_equal_symmetric.
    Variable abst_T : Set.
    Let abst_equal := equal
    abst_T.
(* File "basic_type.fcl", line 59, characters 2-49 *)
Theorem for_zenon_equal_symmetric:(forall x:abst_T,(forall y:abst_T,((
Is_true (abst_equal x y))->(Is_true (abst_equal y x))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>(forall y:abst_T,((
Is_true (abst_equal x y))->(Is_true (abst_equal y x))))) (fun zenon_Hd=>
(zenon_ex abst_T (fun x:abst_T=>(~(forall y:abst_T,((Is_true (
abst_equal x y))->(Is_true (abst_equal y x)))))) (fun(zenon_Tx_c:abst_T)
 zenon_Hc=>(zenon_notallex (fun y:abst_T=>((Is_true (abst_equal
zenon_Tx_c y))->(Is_true (abst_equal y zenon_Tx_c)))) (fun zenon_Hb=>(
zenon_ex abst_T (fun y:abst_T=>(~((Is_true (abst_equal zenon_Tx_c y))->(
Is_true (abst_equal y zenon_Tx_c))))) (fun(zenon_Ty_d:abst_T) zenon_Ha=>
(zenon_notimply _ _ (fun zenon_H9 zenon_H7=>(let zenon_H8:=zenon_H9 in (
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ zenon_Tx_c
zenon_Ty_d (fun zenon_H4=>(let zenon_H6:=zenon_H7 in (
coq_builtins.zenon_not_syntactic_equal _ zenon_Ty_d zenon_Tx_c (fun
zenon_H5=>(zenon_eqsym _ zenon_Tx_c zenon_Ty_d zenon_H4 zenon_H5))
zenon_H6))) zenon_H8))) zenon_Ha)) zenon_Hb)) zenon_Hc)) zenon_Hd))
zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_symmetric :
      forall x  y : abst_T,
        Is_true ((abst_equal x y)) -> Is_true ((abst_equal y x)).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_equal := abst_equal).
    apply for_zenon_equal_symmetric;
    auto.
    Qed.
    End Proof_of_equal_symmetric.
  
  Theorem equal_symmetric  (abst_T : Set) (abst_equal := equal abst_T):
    forall x  y : abst_T,
      Is_true ((abst_equal x y)) -> Is_true ((abst_equal y x)).
  apply for_zenon_abstracted_equal_symmetric;
  auto.
  Qed.
  
  (* From species basic_type#Int_value. *)
  (* Section for proof of theorem 'equal_transitive'. *)
  Section Proof_of_equal_transitive.
    Variable abst_T : Set.
    Let abst_equal := equal
    abst_T.
(* File "basic_type.fcl", line 56, characters 2-50 *)
Theorem for_zenon_equal_transitive:(forall x:abst_T,(forall y:abst_T,(
forall z:abst_T,((Is_true (abst_equal x y))->((Is_true (abst_equal y z))
->(Is_true (abst_equal x z))))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>(forall y:abst_T,(
forall z:abst_T,((Is_true (abst_equal x y))->((Is_true (abst_equal y z))
->(Is_true (abst_equal x z))))))) (fun zenon_H15=>(zenon_ex abst_T (fun
x:abst_T=>(~(forall y:abst_T,(forall z:abst_T,((Is_true (abst_equal x y)
)->((Is_true (abst_equal y z))->(Is_true (abst_equal x z)))))))) (fun(
zenon_Tx_c:abst_T) zenon_H14=>(zenon_notallex (fun y:abst_T=>(forall z
:abst_T,((Is_true (abst_equal zenon_Tx_c y))->((Is_true (abst_equal y z)
)->(Is_true (abst_equal zenon_Tx_c z)))))) (fun zenon_H13=>(zenon_ex
abst_T (fun y:abst_T=>(~(forall z:abst_T,((Is_true (abst_equal
zenon_Tx_c y))->((Is_true (abst_equal y z))->(Is_true (abst_equal
zenon_Tx_c z))))))) (fun(zenon_Ty_d:abst_T) zenon_H12=>(zenon_notallex (
fun z:abst_T=>((Is_true (abst_equal zenon_Tx_c zenon_Ty_d))->((Is_true (
abst_equal zenon_Ty_d z))->(Is_true (abst_equal zenon_Tx_c z))))) (fun
zenon_H11=>(zenon_ex abst_T (fun z:abst_T=>(~((Is_true (abst_equal
zenon_Tx_c zenon_Ty_d))->((Is_true (abst_equal zenon_Ty_d z))->(Is_true
(abst_equal zenon_Tx_c z)))))) (fun(zenon_Tz_e:abst_T) zenon_H10=>(
zenon_notimply _ _ (fun zenon_He zenon_Hf=>(zenon_notimply _ _ (fun
zenon_Hc zenon_Ha=>(let zenon_Hd:=zenon_He in (
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ zenon_Tx_c
zenon_Ty_d (fun zenon_H6=>(let zenon_Hb:=zenon_Hc in (
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ zenon_Ty_d
zenon_Tz_e (fun zenon_H7=>(let zenon_H9:=zenon_Ha in (
coq_builtins.zenon_not_syntactic_equal _ zenon_Tx_c zenon_Tz_e (fun
zenon_H5=>(zenon_subst _ (fun zenon_Vf=>(zenon_Tx_c = zenon_Vf))
zenon_Ty_d zenon_Tz_e (fun zenon_H8=>(zenon_H8 zenon_H7)) zenon_H5
zenon_H6)) zenon_H9))) zenon_Hb))) zenon_Hd))) zenon_Hf)) zenon_H10))
zenon_H11)) zenon_H12)) zenon_H13)) zenon_H14)) zenon_H15)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_transitive :
      forall x  y  z : abst_T,
        Is_true ((abst_equal x y)) ->
          Is_true ((abst_equal y z)) -> Is_true ((abst_equal x z)).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_equal := abst_equal).
    apply for_zenon_equal_transitive;
    auto.
    Qed.
    End Proof_of_equal_transitive.
  
  Theorem equal_transitive  (abst_T : Set) (abst_equal := equal abst_T):
    forall x  y  z : abst_T,
      Is_true ((abst_equal x y)) ->
        Is_true ((abst_equal y z)) -> Is_true ((abst_equal x z)).
  apply for_zenon_abstracted_equal_transitive;
  auto.
  Qed.
  
  (* Fully defined 'Int_value' species's collection generator. *)
  Definition collection_create :=
    let local_rep := basics.int__t in
    (* From species basic_type#Int_value. *)
    let local_element := element in
    (* From species basic_type#Int_value. *)
    let local_equal := equal local_rep in
    (* From species basic_type#Int_value. *)
    let local_geq := geq in
    (* From species basic_type#Int_value. *)
    let local_of_int := of_int in
    (* From species basic_type#Int_value. *)
    let local_parse := parse in
    (* From species basic_type#Int_value. *)
    let local_plus := plus in
    (* From species basic_type#Int_value. *)
    let local_pos := pos in
    (* From species basic_type#Int_value. *)
    let local_print := print in
    (* From species sets#Setoid. *)
    let local_different := sets.Setoid.different local_rep local_equal in
    (* From species basic_type#Int_value. *)
    let local_equal_reflexive := equal_reflexive local_rep in
    (* From species basic_type#Int_value. *)
    let local_equal_symmetric := equal_symmetric local_rep in
    (* From species basic_type#Int_value. *)
    let local_equal_transitive := equal_transitive local_rep in
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
    mk_record local_rep local_element local_equal local_geq local_of_int
    local_parse local_plus local_pos local_print local_different
    local_equal_reflexive local_equal_symmetric local_equal_transitive
    local_same_is_not_different local_different_is_complete
    local_different_is_irreflexive local_different_is_symmetric.
  
End Int_value.

Module Coll_int_value.
  Let effective_collection := Int_value.collection_create.
  (* Carrier's structure explicitly given by "rep". *)
  Definition me_as_carrier := basics.int__t.
  Definition element := effective_collection.(Int_value.rf_element).
  Definition equal := effective_collection.(Int_value.rf_equal).
  Definition geq := effective_collection.(Int_value.rf_geq).
  Definition of_int := effective_collection.(Int_value.rf_of_int).
  Definition parse := effective_collection.(Int_value.rf_parse).
  Definition plus := effective_collection.(Int_value.rf_plus).
  Definition pos := effective_collection.(Int_value.rf_pos).
  Definition print := effective_collection.(Int_value.rf_print).
  Definition different := effective_collection.(Int_value.rf_different).
  Definition equal_reflexive :=
    effective_collection.(Int_value.rf_equal_reflexive).
  Definition equal_symmetric :=
    effective_collection.(Int_value.rf_equal_symmetric).
  Definition equal_transitive :=
    effective_collection.(Int_value.rf_equal_transitive).
  Definition same_is_not_different :=
    effective_collection.(Int_value.rf_same_is_not_different).
  Definition different_is_complete :=
    effective_collection.(Int_value.rf_different_is_complete).
  Definition different_is_irreflexive :=
    effective_collection.(Int_value.rf_different_is_irreflexive).
  Definition different_is_symmetric :=
    effective_collection.(Int_value.rf_different_is_symmetric).
  
End Coll_int_value.

Module Bool_value.
  Record me_as_species : Type :=
    mk_record {
    rf_T : Set ;
    (* From species basic_type#Bool_value. *)
    rf_element : rf_T ;
    (* From species basic_type#Bool_value. *)
    rf_equal : rf_T -> rf_T -> basics.bool__t ;
    (* From species basic_type#Bool_value. *)
    rf_of_bool : basics.bool__t -> rf_T ;
    (* From species basic_type#Bool_value. *)
    rf_parse : basics.string__t -> rf_T ;
    (* From species sets#Setoid. *)
    rf_different : rf_T -> rf_T -> basics.bool__t ;
    (* From species basic_type#Bool_value. *)
    rf_equal_reflexive : forall x : rf_T, Is_true ((rf_equal x x)) ;
    (* From species basic_type#Bool_value. *)
    rf_equal_symmetric :
      forall x  y : rf_T,
        Is_true ((rf_equal x y)) -> Is_true ((rf_equal y x)) ;
    (* From species basic_type#Bool_value. *)
    rf_equal_transitive :
      forall x  y  z : rf_T,
        Is_true ((rf_equal x y)) ->
          Is_true ((rf_equal y z)) -> Is_true ((rf_equal x z)) ;
    (* From species basic_type#Bool_value. *)
    rf_print : rf_T -> basics.string__t ;
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
  
  Definition element (abst_T := basics.bool__t) : abst_T := true.
  Definition equal (abst_T : Set) (x : abst_T) (y : abst_T) :
    basics.bool__t := ((basics.syntactic_equal _) x y).
  Definition of_bool (abst_T := basics.bool__t) (b : basics.bool__t) :
    abst_T := b.
  Definition parse (abst_T := basics.bool__t) (x : basics.string__t) :
    abst_T :=
    (if ((basics.syntactic_equal _) x "True"%string) then true else false).
  
  (* From species basic_type#Bool_value. *)
  (* Section for proof of theorem 'equal_reflexive'. *)
  Section Proof_of_equal_reflexive.
    Variable abst_T : Set.
    Let abst_equal := equal
    abst_T.
(* File "basic_type.fcl", line 102, characters 2-49 *)
Theorem for_zenon_equal_reflexive:(forall x:abst_T,(Is_true (abst_equal
x x))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>(Is_true (
abst_equal x x))) (fun zenon_H6=>(zenon_ex abst_T (fun x:abst_T=>(~(
Is_true (abst_equal x x)))) (fun(zenon_Tx_c:abst_T) zenon_H5=>(let
zenon_H4:=zenon_H5 in (coq_builtins.zenon_not_syntactic_equal _
zenon_Tx_c zenon_Tx_c (fun zenon_H3=>(zenon_noteq _ zenon_Tx_c zenon_H3)
) zenon_H4))) zenon_H6)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_reflexive :
      forall x : abst_T, Is_true ((abst_equal x x)).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_equal := abst_equal).
    apply for_zenon_equal_reflexive;
    auto.
    Qed.
    End Proof_of_equal_reflexive.
  
  Theorem equal_reflexive  (abst_T : Set) (abst_equal := equal abst_T):
    forall x : abst_T, Is_true ((abst_equal x x)).
  apply for_zenon_abstracted_equal_reflexive;
  auto.
  Qed.
  
  (* From species basic_type#Bool_value. *)
  (* Section for proof of theorem 'equal_symmetric'. *)
  Section Proof_of_equal_symmetric.
    Variable abst_T : Set.
    Let abst_equal := equal
    abst_T.
(* File "basic_type.fcl", line 99, characters 2-49 *)
Theorem for_zenon_equal_symmetric:(forall x:abst_T,(forall y:abst_T,((
Is_true (abst_equal x y))->(Is_true (abst_equal y x))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>(forall y:abst_T,((
Is_true (abst_equal x y))->(Is_true (abst_equal y x))))) (fun zenon_Hd=>
(zenon_ex abst_T (fun x:abst_T=>(~(forall y:abst_T,((Is_true (
abst_equal x y))->(Is_true (abst_equal y x)))))) (fun(zenon_Tx_c:abst_T)
 zenon_Hc=>(zenon_notallex (fun y:abst_T=>((Is_true (abst_equal
zenon_Tx_c y))->(Is_true (abst_equal y zenon_Tx_c)))) (fun zenon_Hb=>(
zenon_ex abst_T (fun y:abst_T=>(~((Is_true (abst_equal zenon_Tx_c y))->(
Is_true (abst_equal y zenon_Tx_c))))) (fun(zenon_Ty_d:abst_T) zenon_Ha=>
(zenon_notimply _ _ (fun zenon_H9 zenon_H7=>(let zenon_H8:=zenon_H9 in (
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ zenon_Tx_c
zenon_Ty_d (fun zenon_H4=>(let zenon_H6:=zenon_H7 in (
coq_builtins.zenon_not_syntactic_equal _ zenon_Ty_d zenon_Tx_c (fun
zenon_H5=>(zenon_eqsym _ zenon_Tx_c zenon_Ty_d zenon_H4 zenon_H5))
zenon_H6))) zenon_H8))) zenon_Ha)) zenon_Hb)) zenon_Hc)) zenon_Hd))
zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_symmetric :
      forall x  y : abst_T,
        Is_true ((abst_equal x y)) -> Is_true ((abst_equal y x)).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_equal := abst_equal).
    apply for_zenon_equal_symmetric;
    auto.
    Qed.
    End Proof_of_equal_symmetric.
  
  Theorem equal_symmetric  (abst_T : Set) (abst_equal := equal abst_T):
    forall x  y : abst_T,
      Is_true ((abst_equal x y)) -> Is_true ((abst_equal y x)).
  apply for_zenon_abstracted_equal_symmetric;
  auto.
  Qed.
  
  (* From species basic_type#Bool_value. *)
  (* Section for proof of theorem 'equal_transitive'. *)
  Section Proof_of_equal_transitive.
    Variable abst_T : Set.
    Let abst_equal := equal
    abst_T.
(* File "basic_type.fcl", line 96, characters 2-50 *)
Theorem for_zenon_equal_transitive:(forall x:abst_T,(forall y:abst_T,(
forall z:abst_T,((Is_true (abst_equal x y))->((Is_true (abst_equal y z))
->(Is_true (abst_equal x z))))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>(forall y:abst_T,(
forall z:abst_T,((Is_true (abst_equal x y))->((Is_true (abst_equal y z))
->(Is_true (abst_equal x z))))))) (fun zenon_H15=>(zenon_ex abst_T (fun
x:abst_T=>(~(forall y:abst_T,(forall z:abst_T,((Is_true (abst_equal x y)
)->((Is_true (abst_equal y z))->(Is_true (abst_equal x z)))))))) (fun(
zenon_Tx_c:abst_T) zenon_H14=>(zenon_notallex (fun y:abst_T=>(forall z
:abst_T,((Is_true (abst_equal zenon_Tx_c y))->((Is_true (abst_equal y z)
)->(Is_true (abst_equal zenon_Tx_c z)))))) (fun zenon_H13=>(zenon_ex
abst_T (fun y:abst_T=>(~(forall z:abst_T,((Is_true (abst_equal
zenon_Tx_c y))->((Is_true (abst_equal y z))->(Is_true (abst_equal
zenon_Tx_c z))))))) (fun(zenon_Ty_d:abst_T) zenon_H12=>(zenon_notallex (
fun z:abst_T=>((Is_true (abst_equal zenon_Tx_c zenon_Ty_d))->((Is_true (
abst_equal zenon_Ty_d z))->(Is_true (abst_equal zenon_Tx_c z))))) (fun
zenon_H11=>(zenon_ex abst_T (fun z:abst_T=>(~((Is_true (abst_equal
zenon_Tx_c zenon_Ty_d))->((Is_true (abst_equal zenon_Ty_d z))->(Is_true
(abst_equal zenon_Tx_c z)))))) (fun(zenon_Tz_e:abst_T) zenon_H10=>(
zenon_notimply _ _ (fun zenon_He zenon_Hf=>(zenon_notimply _ _ (fun
zenon_Hc zenon_Ha=>(let zenon_Hd:=zenon_He in (
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ zenon_Tx_c
zenon_Ty_d (fun zenon_H6=>(let zenon_Hb:=zenon_Hc in (
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ zenon_Ty_d
zenon_Tz_e (fun zenon_H7=>(let zenon_H9:=zenon_Ha in (
coq_builtins.zenon_not_syntactic_equal _ zenon_Tx_c zenon_Tz_e (fun
zenon_H5=>(zenon_subst _ (fun zenon_Vf=>(zenon_Tx_c = zenon_Vf))
zenon_Ty_d zenon_Tz_e (fun zenon_H8=>(zenon_H8 zenon_H7)) zenon_H5
zenon_H6)) zenon_H9))) zenon_Hb))) zenon_Hd))) zenon_Hf)) zenon_H10))
zenon_H11)) zenon_H12)) zenon_H13)) zenon_H14)) zenon_H15)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_transitive :
      forall x  y  z : abst_T,
        Is_true ((abst_equal x y)) ->
          Is_true ((abst_equal y z)) -> Is_true ((abst_equal x z)).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_equal := abst_equal).
    apply for_zenon_equal_transitive;
    auto.
    Qed.
    End Proof_of_equal_transitive.
  
  Theorem equal_transitive  (abst_T : Set) (abst_equal := equal abst_T):
    forall x  y  z : abst_T,
      Is_true ((abst_equal x y)) ->
        Is_true ((abst_equal y z)) -> Is_true ((abst_equal x z)).
  apply for_zenon_abstracted_equal_transitive;
  auto.
  Qed.
  Definition print (abst_T := basics.bool__t)
    (abst_equal : abst_T -> abst_T -> basics.bool__t) (x : abst_T) :
    basics.string__t :=
    (if (abst_equal x true) then "True"%string else "False"%string).
  
  (* Fully defined 'Bool_value' species's collection generator. *)
  Definition collection_create :=
    let local_rep := basics.bool__t in
    (* From species basic_type#Bool_value. *)
    let local_element := element in
    (* From species basic_type#Bool_value. *)
    let local_equal := equal local_rep in
    (* From species basic_type#Bool_value. *)
    let local_of_bool := of_bool in
    (* From species basic_type#Bool_value. *)
    let local_parse := parse in
    (* From species sets#Setoid. *)
    let local_different := sets.Setoid.different local_rep local_equal in
    (* From species basic_type#Bool_value. *)
    let local_equal_reflexive := equal_reflexive local_rep in
    (* From species basic_type#Bool_value. *)
    let local_equal_symmetric := equal_symmetric local_rep in
    (* From species basic_type#Bool_value. *)
    let local_equal_transitive := equal_transitive local_rep in
    (* From species basic_type#Bool_value. *)
    let local_print := print local_equal in
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
    mk_record local_rep local_element local_equal local_of_bool local_parse
    local_different local_equal_reflexive local_equal_symmetric
    local_equal_transitive local_print local_same_is_not_different
    local_different_is_complete local_different_is_irreflexive
    local_different_is_symmetric.
  
End Bool_value.

Module Coll_bool_value.
  Let effective_collection := Bool_value.collection_create.
  (* Carrier's structure explicitly given by "rep". *)
  Definition me_as_carrier := basics.bool__t.
  Definition element := effective_collection.(Bool_value.rf_element).
  Definition equal := effective_collection.(Bool_value.rf_equal).
  Definition of_bool := effective_collection.(Bool_value.rf_of_bool).
  Definition parse := effective_collection.(Bool_value.rf_parse).
  Definition different := effective_collection.(Bool_value.rf_different).
  Definition equal_reflexive :=
    effective_collection.(Bool_value.rf_equal_reflexive).
  Definition equal_symmetric :=
    effective_collection.(Bool_value.rf_equal_symmetric).
  Definition equal_transitive :=
    effective_collection.(Bool_value.rf_equal_transitive).
  Definition print := effective_collection.(Bool_value.rf_print).
  Definition same_is_not_different :=
    effective_collection.(Bool_value.rf_same_is_not_different).
  Definition different_is_complete :=
    effective_collection.(Bool_value.rf_different_is_complete).
  Definition different_is_irreflexive :=
    effective_collection.(Bool_value.rf_different_is_irreflexive).
  Definition different_is_symmetric :=
    effective_collection.(Bool_value.rf_different_is_symmetric).
  
End Coll_bool_value.

