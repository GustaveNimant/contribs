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
Module Sp_pair.
  
End Sp_pair.

Module Imp_pair.
  Record me_as_species (S1_T : Set) (S2_T : Set) (_p_S1_equal : S1_T ->
                                                                  S1_T ->
                                                                    basics.bool__t)
    (_p_S2_equal : S2_T -> S2_T -> basics.bool__t) : Type :=
    mk_record {
    rf_T : Set ;
    (* From species pair#Imp_pair. *)
    rf_constr : S1_T -> S2_T -> rf_T ;
    (* From species pair#Imp_pair. *)
    rf_equal : rf_T -> rf_T -> basics.bool__t ;
    (* From species basics#Basic_object. *)
    rf_parse : basics.string__t -> rf_T ;
    (* From species basics#Basic_object. *)
    rf_print : rf_T -> basics.string__t ;
    (* From species pair#Imp_pair. *)
    rf_prj_a : rf_T -> S1_T ;
    (* From species pair#Imp_pair. *)
    rf_prj_b : rf_T -> S2_T ;
    (* From species pair#Imp_pair. *)
    rf_element : rf_T ;
    (* From species sets#Setoid. *)
    rf_different : rf_T -> rf_T -> basics.bool__t ;
    (* From species pair#Imp_pair. *)
    rf_prj_a_is_first_of_pair :
      forall n1 : S1_T,
        forall n2 : S2_T,
          Is_true ((_p_S1_equal (rf_prj_a (rf_constr n1 n2)) n1)) ;
    (* From species pair#Imp_pair. *)
    rf_def_equal :
      forall p1  p2 : rf_T,
        Is_true ((rf_equal p1 p2)) <->
          (Is_true ((_p_S1_equal (rf_prj_a p1) (rf_prj_a p2))) /\
             Is_true ((_p_S2_equal (rf_prj_b p1) (rf_prj_b p2)))) ;
    (* From species pair#Imp_pair. *)
    rf_prj_b_is_snd_of_pair :
      forall n1 : S1_T,
        forall n2 : S2_T,
          Is_true ((_p_S2_equal (rf_prj_b (rf_constr n1 n2)) n2)) ;
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
    (* From species pair#Imp_pair. *)
    rf_equal_transitive :
      forall x  y  z : rf_T,
        Is_true ((rf_equal x y)) ->
          Is_true ((rf_equal y z)) -> Is_true ((rf_equal x z)) ;
    (* From species pair#Imp_pair. *)
    rf_def_equal1 :
      forall n1  n3 : S1_T,
        forall n2  n4 : S2_T,
          Is_true ((rf_equal (rf_constr n1 n2) (rf_constr n3 n4))) <->
            (Is_true ((_p_S1_equal n1 n3)) /\ Is_true ((_p_S2_equal n2 n4))) ;
    (* From species pair#Imp_pair. *)
    rf_equal_reflexive : forall x : rf_T, Is_true ((rf_equal x x)) ;
    (* From species pair#Imp_pair. *)
    rf_equal_reflexive2 :
      forall n1 : S1_T,
        forall n2 : S2_T,
          Is_true ((rf_equal (rf_constr n1 n2) (rf_constr n1 n2))) ;
    (* From species pair#Imp_pair. *)
    rf_equal_symmetric2 :
      forall n1  n3 : S1_T,
        forall n2  n4 : S2_T,
          Is_true ((rf_equal (rf_constr n1 n2) (rf_constr n3 n4))) ->
            Is_true ((rf_equal (rf_constr n3 n4) (rf_constr n1 n2))) ;
    (* From species pair#Imp_pair. *)
    rf_equal_transitive2 :
      forall n1  n3  n5 : S1_T,
        forall n2  n4  n6 : S2_T,
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
  
  Definition constr (_p_S1_T : Set) (_p_S2_T : Set)
    (abst_T := (Datatypes.prod _p_S1_T _p_S2_T)) (n1 : _p_S1_T)
    (n2 : _p_S2_T) : abst_T := ((basics.pair _ _) n1 n2).
  Definition equal (_p_S1_T : Set) (_p_S2_T : Set) (_p_S1_equal :
    _p_S1_T -> _p_S1_T -> basics.bool__t) (_p_S2_equal :
    _p_S2_T -> _p_S2_T -> basics.bool__t)
    (abst_T := (Datatypes.prod _p_S1_T _p_S2_T)) (n1 : abst_T)
    (n2 : abst_T) : basics.bool__t :=
    (basics._amper__amper_
      ((_p_S1_equal ((basics.fst _ _) n1) ((basics.fst _ _) n2)))
      ((_p_S2_equal ((basics.snd _ _) n1) ((basics.snd _ _) n2)))).
  Definition prj_a (_p_S1_T : Set) (_p_S2_T : Set)
    (abst_T := (Datatypes.prod _p_S1_T _p_S2_T)) (nn : abst_T) : _p_S1_T :=
    ((basics.fst _ _) nn).
  Definition prj_b (_p_S1_T : Set) (_p_S2_T : Set)
    (abst_T := (Datatypes.prod _p_S1_T _p_S2_T)) (nn : abst_T) : _p_S2_T :=
    ((basics.snd _ _) nn).
  Definition element (_p_S1_T : Set) (_p_S2_T : Set) (_p_S1_element :
    _p_S1_T) (_p_S2_element : _p_S2_T) (abst_T : Set)
    (abst_constr : _p_S1_T -> _p_S2_T -> abst_T) : abst_T :=
    (abst_constr _p_S1_element _p_S2_element).
  
  (* From species pair#Imp_pair. *)
  Theorem prj_a_is_first_of_pair  (_p_S1_T : Set) (_p_S2_T : Set)
    (_p_S1_equal : _p_S1_T -> _p_S1_T -> basics.bool__t) (abst_T : Set)
    (abst_constr : _p_S1_T -> _p_S2_T -> abst_T)
    (abst_prj_a : abst_T -> _p_S1_T):
    forall n1 : _p_S1_T,
      forall n2 : _p_S2_T,
        Is_true ((_p_S1_equal (abst_prj_a (abst_constr n1 n2)) n1)).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
  (* From species pair#Imp_pair. *)
  Theorem def_equal  (_p_S1_T : Set) (_p_S2_T : Set) (_p_S1_equal :
    _p_S1_T -> _p_S1_T -> basics.bool__t) (_p_S2_equal :
    _p_S2_T -> _p_S2_T -> basics.bool__t) (abst_T : Set)
    (abst_equal : abst_T -> abst_T -> basics.bool__t)
    (abst_prj_a : abst_T -> _p_S1_T) (abst_prj_b : abst_T -> _p_S2_T):
    forall p1  p2 : abst_T,
      Is_true ((abst_equal p1 p2)) <->
        (Is_true ((_p_S1_equal (abst_prj_a p1) (abst_prj_a p2))) /\
           Is_true ((_p_S2_equal (abst_prj_b p1) (abst_prj_b p2)))).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
  (* From species pair#Imp_pair. *)
  Theorem prj_b_is_snd_of_pair  (_p_S1_T : Set) (_p_S2_T : Set)
    (_p_S2_equal : _p_S2_T -> _p_S2_T -> basics.bool__t) (abst_T : Set)
    (abst_constr : _p_S1_T -> _p_S2_T -> abst_T)
    (abst_prj_b : abst_T -> _p_S2_T):
    forall n1 : _p_S1_T,
      forall n2 : _p_S2_T,
        Is_true ((_p_S2_equal (abst_prj_b (abst_constr n1 n2)) n2)).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
  (* From species pair#Imp_pair. *)
  Theorem unicite_1  (_p_S1_T : Set) (_p_S2_T : Set) (abst_T : Set)
    (abst_constr : _p_S1_T -> _p_S2_T -> abst_T)
    (abst_equal : abst_T -> abst_T -> basics.bool__t)
    (abst_prj_a : abst_T -> _p_S1_T) (abst_prj_b : abst_T -> _p_S2_T):
    forall a : abst_T,
      Is_true ((abst_equal (abst_constr (abst_prj_a a) (abst_prj_b a)) a)).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
  (* From species pair#Imp_pair. *)
  Theorem unicite_2  (_p_S1_T : Set) (_p_S2_T : Set) (abst_T : Set)
    (abst_constr : _p_S1_T -> _p_S2_T -> abst_T)
    (abst_equal : abst_T -> abst_T -> basics.bool__t)
    (abst_prj_a : abst_T -> _p_S1_T) (abst_prj_b : abst_T -> _p_S2_T):
    forall a : abst_T,
      Is_true ((abst_equal a (abst_constr (abst_prj_a a) (abst_prj_b a)))).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
  (* From species pair#Imp_pair. *)
  (* Section for proof of theorem 'equal_transitive'. *)
  Section Proof_of_equal_transitive.
    Variable _p_S1_T : Set.
    Variable _p_S2_T : Set.
    Variable _p_S1_equal : _p_S1_T -> _p_S1_T -> basics.bool__t.
    Variable _p_S1_equal_transitive :
      forall x  y  z : _p_S1_T,
        Is_true ((_p_S1_equal x y)) ->
          Is_true ((_p_S1_equal y z)) -> Is_true ((_p_S1_equal x z)).
    Variable _p_S2_equal : _p_S2_T -> _p_S2_T -> basics.bool__t.
    Variable _p_S2_equal_transitive :
      forall x  y  z : _p_S2_T,
        Is_true ((_p_S2_equal x y)) ->
          Is_true ((_p_S2_equal y z)) -> Is_true ((_p_S2_equal x z)).
    Variable abst_T : Set.
    Variable abst_equal : abst_T -> abst_T -> basics.bool__t.
    Variable abst_prj_a : abst_T -> _p_S1_T.
    Variable abst_prj_b : abst_T -> _p_S2_T.
    Hypothesis abst_def_equal :
      forall p1  p2 : abst_T,
        Is_true ((abst_equal p1 p2)) <->
          (Is_true ((_p_S1_equal (abst_prj_a p1) (abst_prj_a p2))) /\
             Is_true ((_p_S2_equal (abst_prj_b p1) (abst_prj_b p2)))).
    Section __A_1.
      Variable p1 : abst_T.
      Variable p2 : abst_T.
      Variable p3 : abst_T.
      Variable H1 : Is_true ((abst_equal p1 p2)).
      Variable H2 : Is_true ((abst_equal p2 p3)).
      Section __A_1_1.
(* File "pair.fcl", line 279, characters 9-44 *)
Theorem for_zenon___A_1_1_LEMMA:((Is_true (_p_S1_equal (abst_prj_a p1) (
abst_prj_a p2)))/\(Is_true (_p_S2_equal (abst_prj_b p1) (abst_prj_b p2))
)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all abst_T (fun p1:abst_T=>(forall p2
:abst_T,((Is_true (abst_equal p1 p2))<->((Is_true (_p_S1_equal (
abst_prj_a p1) (abst_prj_a p2)))/\(Is_true (_p_S2_equal (abst_prj_b p1)
(abst_prj_b p2))))))) p1 (fun zenon_H6=>(zenon_all abst_T (fun p2
:abst_T=>((Is_true (abst_equal p1 p2))<->((Is_true (_p_S1_equal (
abst_prj_a p1) (abst_prj_a p2)))/\(Is_true (_p_S2_equal (abst_prj_b p1)
(abst_prj_b p2)))))) p2 (fun zenon_H5=>(zenon_equiv _ _ (fun zenon_H4
zenon_G=>(zenon_H4 H1)) (fun H1 zenon_H3=>(zenon_G zenon_H3)) zenon_H5))
 zenon_H6)) abst_def_equal)))).
Qed.

        Theorem __A_1_1_LEMMA :
          (Is_true ((_p_S1_equal (abst_prj_a p1) (abst_prj_a p2))) /\
             Is_true ((_p_S2_equal (abst_prj_b p1) (abst_prj_b p2)))).
        assert (__force_use_H1 := H1).
        assert (__force_use_H2 := H2).
        apply for_zenon___A_1_1_LEMMA;
        auto.
        Qed.
        End __A_1_1.
      Section __A_1_2.
(* File "pair.fcl", line 281, characters 9-44 *)
Theorem for_zenon___A_1_2_LEMMA:((Is_true (_p_S1_equal (abst_prj_a p2) (
abst_prj_a p3)))/\(Is_true (_p_S2_equal (abst_prj_b p2) (abst_prj_b p3))
)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all abst_T (fun p1:abst_T=>(forall p2
:abst_T,((Is_true (abst_equal p1 p2))<->((Is_true (_p_S1_equal (
abst_prj_a p1) (abst_prj_a p2)))/\(Is_true (_p_S2_equal (abst_prj_b p1)
(abst_prj_b p2))))))) p2 (fun zenon_H6=>(zenon_all abst_T (fun zenon_Vg
:abst_T=>((Is_true (abst_equal p2 zenon_Vg))<->((Is_true (_p_S1_equal (
abst_prj_a p2) (abst_prj_a zenon_Vg)))/\(Is_true (_p_S2_equal (
abst_prj_b p2) (abst_prj_b zenon_Vg)))))) p3 (fun zenon_H5=>(
zenon_equiv _ _ (fun zenon_H4 zenon_G=>(zenon_H4 H2)) (fun H2 zenon_H3=>
(zenon_G zenon_H3)) zenon_H5)) zenon_H6)) abst_def_equal)))).
Qed.

        Theorem __A_1_2_LEMMA :
          (Is_true ((_p_S1_equal (abst_prj_a p2) (abst_prj_a p3))) /\
             Is_true ((_p_S2_equal (abst_prj_b p2) (abst_prj_b p3)))).
        assert (__force_use_H1 := H1).
        assert (__force_use_H2 := H2).
        apply for_zenon___A_1_2_LEMMA;
        auto.
        Qed.
        End __A_1_2.
      Section __A_1_3.
(* File "pair.fcl", line 283, characters 6-74 *)
Theorem for_zenon___A_1_3_LEMMA:((Is_true (_p_S1_equal (abst_prj_a p1) (
abst_prj_a p3)))/\(Is_true (_p_S2_equal (abst_prj_b p1) (abst_prj_b p3))
)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_and _ _ (fun zenon_H14 zenon_Ha=>(
zenon_and _ _ (fun zenon_H11 zenon_H7=>(zenon_notand _ _ (fun
zenon_H10=>(zenon_all _p_S1_T (fun x:_p_S1_T=>(forall y:_p_S1_T,(forall
z:_p_S1_T,((Is_true (_p_S1_equal x y))->((Is_true (_p_S1_equal y z))->(
Is_true (_p_S1_equal x z))))))) (abst_prj_a p1) (fun zenon_H18=>(
zenon_all _p_S1_T (fun y:_p_S1_T=>(forall z:_p_S1_T,((Is_true (
_p_S1_equal (abst_prj_a p1) y))->((Is_true (_p_S1_equal y z))->(Is_true
(_p_S1_equal (abst_prj_a p1) z)))))) (abst_prj_a p2) (fun zenon_H17=>(
zenon_all _p_S1_T (fun z:_p_S1_T=>((Is_true (_p_S1_equal (abst_prj_a p1)
 (abst_prj_a p2)))->((Is_true (_p_S1_equal (abst_prj_a p2) z))->(
Is_true (_p_S1_equal (abst_prj_a p1) z))))) (abst_prj_a p3) (fun
zenon_H16=>(zenon_imply _ _ (fun zenon_H15=>(zenon_H15 zenon_H14)) (fun
zenon_H13=>(zenon_imply _ _ (fun zenon_H12=>(zenon_H12 zenon_H11)) (fun
zenon_Hf=>(zenon_H10 zenon_Hf)) zenon_H13)) zenon_H16)) zenon_H17))
zenon_H18)) _p_S1_equal_transitive)) (fun zenon_H6=>(zenon_all _p_S2_T (
fun x:_p_S2_T=>(forall y:_p_S2_T,(forall z:_p_S2_T,((Is_true (
_p_S2_equal x y))->((Is_true (_p_S2_equal y z))->(Is_true (_p_S2_equal
x z))))))) (abst_prj_b p1) (fun zenon_He=>(zenon_all _p_S2_T (fun y
:_p_S2_T=>(forall z:_p_S2_T,((Is_true (_p_S2_equal (abst_prj_b p1) y))->
((Is_true (_p_S2_equal y z))->(Is_true (_p_S2_equal (abst_prj_b p1) z)))
))) (abst_prj_b p2) (fun zenon_Hd=>(zenon_all _p_S2_T (fun z:_p_S2_T=>((
Is_true (_p_S2_equal (abst_prj_b p1) (abst_prj_b p2)))->((Is_true (
_p_S2_equal (abst_prj_b p2) z))->(Is_true (_p_S2_equal (abst_prj_b p1)
z))))) (abst_prj_b p3) (fun zenon_Hc=>(zenon_imply _ _ (fun zenon_Hb=>(
zenon_Hb zenon_Ha)) (fun zenon_H9=>(zenon_imply _ _ (fun zenon_H8=>(
zenon_H8 zenon_H7)) (fun zenon_H5=>(zenon_H6 zenon_H5)) zenon_H9))
zenon_Hc)) zenon_Hd)) zenon_He)) _p_S2_equal_transitive)) zenon_G))
__A_1_2_LEMMA)) __A_1_1_LEMMA)))).
Qed.

        Theorem __A_1_3_LEMMA :
          (Is_true ((_p_S1_equal (abst_prj_a p1) (abst_prj_a p3))) /\
             Is_true ((_p_S2_equal (abst_prj_b p1) (abst_prj_b p3)))).
        assert (__force_use_H1 := H1).
        assert (__force_use_H2 := H2).
        apply for_zenon___A_1_3_LEMMA;
        auto.
        Qed.
        End __A_1_3.
(* File "pair.fcl", line 284, characters 13-44 *)
Theorem for_zenon___A_1_LEMMA:(Is_true (abst_equal p1 p3)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all abst_T (fun p1:abst_T=>(forall p2
:abst_T,((Is_true (abst_equal p1 p2))<->((Is_true (_p_S1_equal (
abst_prj_a p1) (abst_prj_a p2)))/\(Is_true (_p_S2_equal (abst_prj_b p1)
(abst_prj_b p2))))))) p1 (fun zenon_H6=>(zenon_all abst_T (fun p2
:abst_T=>((Is_true (abst_equal p1 p2))<->((Is_true (_p_S1_equal (
abst_prj_a p1) (abst_prj_a p2)))/\(Is_true (_p_S2_equal (abst_prj_b p1)
(abst_prj_b p2)))))) p3 (fun zenon_H5=>(zenon_equiv _ _ (fun zenon_G
zenon_H4=>(zenon_H4 __A_1_3_LEMMA)) (fun zenon_H3 __A_1_3_LEMMA=>(
zenon_G zenon_H3)) zenon_H5)) zenon_H6)) abst_def_equal)))).
Qed.

      Theorem __A_1_LEMMA : Is_true ((abst_equal p1 p3)).
      assert (__force_use_H1 := H1).
      assert (__force_use_H2 := H2).
      apply for_zenon___A_1_LEMMA;
      auto.
      Qed.
      End __A_1.
(* File "pair.fcl", line 285, characters 2-15 *)
Theorem for_zenon_equal_transitive:(forall p1:abst_T,(forall p2:abst_T,(
forall p3:abst_T,((Is_true (abst_equal p1 p2))->((Is_true (abst_equal
p2 p3))->(Is_true (abst_equal p1 p3))))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G __A_1_LEMMA)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_transitive :
      forall x  y  z : abst_T,
        Is_true ((abst_equal x y)) ->
          Is_true ((abst_equal y z)) -> Is_true ((abst_equal x z)).
    assert (__force_use_p_S1_T := _p_S1_T).
    assert (__force_use_p_S2_T := _p_S2_T).
    assert (__force_use__p_S1_equal := _p_S1_equal).
    assert (__force_use__p_S1_equal_transitive := _p_S1_equal_transitive).
    assert (__force_use__p_S2_equal := _p_S2_equal).
    assert (__force_use__p_S2_equal_transitive := _p_S2_equal_transitive).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_equal := abst_equal).
    assert (__force_use_abst_prj_a := abst_prj_a).
    assert (__force_use_abst_prj_b := abst_prj_b).
    assert (__force_use_abst_def_equal := abst_def_equal).
    apply for_zenon_equal_transitive;
    auto.
    Qed.
    End Proof_of_equal_transitive.
  
  Theorem equal_transitive  (_p_S1_T : Set) (_p_S2_T : Set) (_p_S1_equal :
    _p_S1_T -> _p_S1_T -> basics.bool__t) (_p_S1_equal_transitive :
    forall x  y  z : _p_S1_T,
      Is_true ((_p_S1_equal x y)) ->
        Is_true ((_p_S1_equal y z)) -> Is_true ((_p_S1_equal x z)))
    (_p_S2_equal : _p_S2_T -> _p_S2_T -> basics.bool__t)
    (_p_S2_equal_transitive :
    forall x  y  z : _p_S2_T,
      Is_true ((_p_S2_equal x y)) ->
        Is_true ((_p_S2_equal y z)) -> Is_true ((_p_S2_equal x z)))
    (abst_T : Set) (abst_equal : abst_T -> abst_T -> basics.bool__t)
    (abst_prj_a : abst_T -> _p_S1_T) (abst_prj_b : abst_T -> _p_S2_T)
    (abst_def_equal :
    forall p1  p2 : abst_T,
      Is_true ((abst_equal p1 p2)) <->
        (Is_true ((_p_S1_equal (abst_prj_a p1) (abst_prj_a p2))) /\
           Is_true ((_p_S2_equal (abst_prj_b p1) (abst_prj_b p2))))):
    forall x  y  z : abst_T,
      Is_true ((abst_equal x y)) ->
        Is_true ((abst_equal y z)) -> Is_true ((abst_equal x z)).
  apply for_zenon_abstracted_equal_transitive;
  auto.
  Qed.
  
  (* From species pair#Imp_pair. *)
  (* Section for proof of theorem 'def_equal1'. *)
  Section Proof_of_def_equal1.
    Variable _p_S1_T : Set.
    Variable _p_S2_T : Set.
    Variable _p_S1_equal : _p_S1_T -> _p_S1_T -> basics.bool__t.
    Variable _p_S1_equal_symmetric :
      forall x  y : _p_S1_T,
        Is_true ((_p_S1_equal x y)) -> Is_true ((_p_S1_equal y x)).
    Variable _p_S1_equal_transitive :
      forall x  y  z : _p_S1_T,
        Is_true ((_p_S1_equal x y)) ->
          Is_true ((_p_S1_equal y z)) -> Is_true ((_p_S1_equal x z)).
    Variable _p_S2_equal : _p_S2_T -> _p_S2_T -> basics.bool__t.
    Variable _p_S2_equal_symmetric :
      forall x  y : _p_S2_T,
        Is_true ((_p_S2_equal x y)) -> Is_true ((_p_S2_equal y x)).
    Variable _p_S2_equal_transitive :
      forall x  y  z : _p_S2_T,
        Is_true ((_p_S2_equal x y)) ->
          Is_true ((_p_S2_equal y z)) -> Is_true ((_p_S2_equal x z)).
    Variable abst_T : Set.
    Variable abst_constr : _p_S1_T -> _p_S2_T -> abst_T.
    Variable abst_equal : abst_T -> abst_T -> basics.bool__t.
    Variable abst_prj_a : abst_T -> _p_S1_T.
    Variable abst_prj_b : abst_T -> _p_S2_T.
    Hypothesis abst_prj_a_is_first_of_pair :
      forall n1 : _p_S1_T,
        forall n2 : _p_S2_T,
          Is_true ((_p_S1_equal (abst_prj_a (abst_constr n1 n2)) n1)).
    Hypothesis abst_def_equal :
      forall p1  p2 : abst_T,
        Is_true ((abst_equal p1 p2)) <->
          (Is_true ((_p_S1_equal (abst_prj_a p1) (abst_prj_a p2))) /\
             Is_true ((_p_S2_equal (abst_prj_b p1) (abst_prj_b p2)))).
    Hypothesis abst_prj_b_is_snd_of_pair :
      forall n1 : _p_S1_T,
        forall n2 : _p_S2_T,
          Is_true ((_p_S2_equal (abst_prj_b (abst_constr n1 n2)) n2)).
    Section __B_1.
      Variable n1 : _p_S1_T.
      Variable n3 : _p_S1_T.
      Variable n2 : _p_S2_T.
      Variable n4 : _p_S2_T.
      Variable H1 :
        Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))).
      Section __B_1_1.
(* File "pair.fcl", line 150, characters 9-44 *)
Theorem for_zenon___B_1_1_LEMMA:((Is_true (_p_S1_equal (abst_prj_a (
abst_constr n1 n2)) (abst_prj_a (abst_constr n3 n4))))/\(Is_true (
_p_S2_equal (abst_prj_b (abst_constr n1 n2)) (abst_prj_b (abst_constr
n3 n4))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all abst_T (fun p1:abst_T=>(forall p2
:abst_T,((Is_true (abst_equal p1 p2))<->((Is_true (_p_S1_equal (
abst_prj_a p1) (abst_prj_a p2)))/\(Is_true (_p_S2_equal (abst_prj_b p1)
(abst_prj_b p2))))))) (abst_constr n1 n2) (fun zenon_H6=>(zenon_all
abst_T (fun p2:abst_T=>((Is_true (abst_equal (abst_constr n1 n2) p2))<->
((Is_true (_p_S1_equal (abst_prj_a (abst_constr n1 n2)) (abst_prj_a p2))
)/\(Is_true (_p_S2_equal (abst_prj_b (abst_constr n1 n2)) (abst_prj_b
p2)))))) (abst_constr n3 n4) (fun zenon_H5=>(zenon_equiv _ _ (fun
zenon_H4 zenon_G=>(zenon_H4 H1)) (fun H1 zenon_H3=>(zenon_G zenon_H3))
zenon_H5)) zenon_H6)) abst_def_equal)))).
Qed.

        Theorem __B_1_1_LEMMA :
          (Is_true ((_p_S1_equal (abst_prj_a (abst_constr n1 n2))
                      (abst_prj_a (abst_constr n3 n4)))) /\
             Is_true ((_p_S2_equal (abst_prj_b (abst_constr n1 n2))
                        (abst_prj_b (abst_constr n3 n4))))).
        assert (__force_use_H1 := H1).
        apply for_zenon___B_1_1_LEMMA;
        auto.
        Qed.
        End __B_1_1.
      Section __B_1_2.
(* File "pair.fcl", line 153, characters 4-16 *)
Theorem for_zenon___B_1_2_LEMMA:(Is_true (_p_S1_equal (abst_prj_a (
abst_constr n1 n2)) (abst_prj_a (abst_constr n3 n4)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_and _ _ (fun zenon_H2 zenon_H3=>(zenon_G
zenon_H2)) __B_1_1_LEMMA)))).
Qed.

        Theorem __B_1_2_LEMMA :
          Is_true ((_p_S1_equal (abst_prj_a (abst_constr n1 n2))
                     (abst_prj_a (abst_constr n3 n4)))).
        assert (__force_use_H1 := H1).
        apply for_zenon___B_1_2_LEMMA;
        auto.
        Qed.
        End __B_1_2.
      Section __B_1_3.
(* File "pair.fcl", line 156, characters 4-16 *)
Theorem for_zenon___B_1_3_LEMMA:(Is_true (_p_S2_equal (abst_prj_b (
abst_constr n1 n2)) (abst_prj_b (abst_constr n3 n4)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_and _ _ (fun zenon_H3 zenon_H2=>(zenon_G
zenon_H2)) __B_1_1_LEMMA)))).
Qed.

        Theorem __B_1_3_LEMMA :
          Is_true ((_p_S2_equal (abst_prj_b (abst_constr n1 n2))
                     (abst_prj_b (abst_constr n3 n4)))).
        assert (__force_use_H1 := H1).
        apply for_zenon___B_1_3_LEMMA;
        auto.
        Qed.
        End __B_1_3.
      Section __B_1_4.
(* File "pair.fcl", line 160, characters 4-69 *)
Theorem for_zenon___B_1_4_LEMMA:(Is_true (_p_S1_equal (abst_prj_a (
abst_constr n1 n2)) n3)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(let zenon_H5:=(fun zenon_H4=>(zenon_all _p_S1_T (
fun x:_p_S1_T=>(forall y:_p_S1_T,(forall z:_p_S1_T,((Is_true (
_p_S1_equal x y))->((Is_true (_p_S1_equal y z))->(Is_true (_p_S1_equal
x z))))))) (abst_prj_a (abst_constr n1 n2)) (fun zenon_Hc=>(zenon_all
_p_S1_T (fun y:_p_S1_T=>(forall z:_p_S1_T,((Is_true (_p_S1_equal (
abst_prj_a (abst_constr n1 n2)) y))->((Is_true (_p_S1_equal y z))->(
Is_true (_p_S1_equal (abst_prj_a (abst_constr n1 n2)) z)))))) (
abst_prj_a (abst_constr n3 n4)) (fun zenon_Hb=>(zenon_all _p_S1_T (fun
z:_p_S1_T=>((Is_true (_p_S1_equal (abst_prj_a (abst_constr n1 n2)) (
abst_prj_a (abst_constr n3 n4))))->((Is_true (_p_S1_equal (abst_prj_a (
abst_constr n3 n4)) z))->(Is_true (_p_S1_equal (abst_prj_a (abst_constr
n1 n2)) z))))) n3 (fun zenon_Ha=>(zenon_imply _ _ (fun zenon_H9=>(
zenon_H9 __B_1_2_LEMMA)) (fun zenon_H8=>(zenon_imply _ _ (fun zenon_H5=>
(zenon_H5 zenon_H4)) (fun zenon_H7=>(zenon_G zenon_H7)) zenon_H8))
zenon_Ha)) zenon_Hb)) zenon_Hc)) _p_S1_equal_transitive)) in (zenon_all
_p_S1_T (fun n1:_p_S1_T=>(forall n2:_p_S2_T,(Is_true (_p_S1_equal (
abst_prj_a (abst_constr n1 n2)) n1)))) n3 (fun zenon_H6=>(zenon_all
_p_S2_T (fun n2:_p_S2_T=>(Is_true (_p_S1_equal (abst_prj_a (abst_constr
n3 n2)) n3))) n4 (fun zenon_H4=>(zenon_H5 zenon_H4)) zenon_H6))
abst_prj_a_is_first_of_pair))))).
Qed.

        Theorem __B_1_4_LEMMA :
          Is_true ((_p_S1_equal (abst_prj_a (abst_constr n1 n2)) n3)).
        assert (__force_use_H1 := H1).
        apply for_zenon___B_1_4_LEMMA;
        auto.
        Qed.
        End __B_1_4.
      Section __B_1_5.
(* File "pair.fcl", line 163, characters 4-68 *)
Theorem for_zenon___B_1_5_LEMMA:(Is_true (_p_S2_equal (abst_prj_b (
abst_constr n1 n2)) n4)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(let zenon_H5:=(fun zenon_H4=>(zenon_all _p_S2_T (
fun x:_p_S2_T=>(forall y:_p_S2_T,(forall z:_p_S2_T,((Is_true (
_p_S2_equal x y))->((Is_true (_p_S2_equal y z))->(Is_true (_p_S2_equal
x z))))))) (abst_prj_b (abst_constr n1 n2)) (fun zenon_Hc=>(zenon_all
_p_S2_T (fun y:_p_S2_T=>(forall z:_p_S2_T,((Is_true (_p_S2_equal (
abst_prj_b (abst_constr n1 n2)) y))->((Is_true (_p_S2_equal y z))->(
Is_true (_p_S2_equal (abst_prj_b (abst_constr n1 n2)) z)))))) (
abst_prj_b (abst_constr n3 n4)) (fun zenon_Hb=>(zenon_all _p_S2_T (fun
z:_p_S2_T=>((Is_true (_p_S2_equal (abst_prj_b (abst_constr n1 n2)) (
abst_prj_b (abst_constr n3 n4))))->((Is_true (_p_S2_equal (abst_prj_b (
abst_constr n3 n4)) z))->(Is_true (_p_S2_equal (abst_prj_b (abst_constr
n1 n2)) z))))) n4 (fun zenon_Ha=>(zenon_imply _ _ (fun zenon_H9=>(
zenon_H9 __B_1_3_LEMMA)) (fun zenon_H8=>(zenon_imply _ _ (fun zenon_H5=>
(zenon_H5 zenon_H4)) (fun zenon_H7=>(zenon_G zenon_H7)) zenon_H8))
zenon_Ha)) zenon_Hb)) zenon_Hc)) _p_S2_equal_transitive)) in (zenon_all
_p_S1_T (fun n1:_p_S1_T=>(forall n2:_p_S2_T,(Is_true (_p_S2_equal (
abst_prj_b (abst_constr n1 n2)) n2)))) n3 (fun zenon_H6=>(zenon_all
_p_S2_T (fun n2:_p_S2_T=>(Is_true (_p_S2_equal (abst_prj_b (abst_constr
n3 n2)) n2))) n4 (fun zenon_H4=>(zenon_H5 zenon_H4)) zenon_H6))
abst_prj_b_is_snd_of_pair))))).
Qed.

        Theorem __B_1_5_LEMMA :
          Is_true ((_p_S2_equal (abst_prj_b (abst_constr n1 n2)) n4)).
        assert (__force_use_H1 := H1).
        apply for_zenon___B_1_5_LEMMA;
        auto.
        Qed.
        End __B_1_5.
      Section __B_1_6.
(* File "pair.fcl", line 166, characters 4-89 *)
Theorem for_zenon___B_1_6_LEMMA:(Is_true (_p_S1_equal n1 n3)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(let zenon_H16:=(fun zenon_H1d=>(zenon_and _ _ (
fun zenon_H14 zenon_Hb=>(zenon_all _p_S1_T (fun n1:_p_S1_T=>(forall n2
:_p_S2_T,(Is_true (_p_S1_equal (abst_prj_a (abst_constr n1 n2)) n1))))
n1 (fun zenon_H1c=>(zenon_all _p_S2_T (fun n2:_p_S2_T=>(Is_true (
_p_S1_equal (abst_prj_a (abst_constr n1 n2)) n1))) n2 (fun zenon_H18=>(
zenon_all _p_S1_T (fun x:_p_S1_T=>(forall y:_p_S1_T,((Is_true (
_p_S1_equal x y))->(Is_true (_p_S1_equal y x))))) (abst_prj_a (
abst_constr n1 n2)) (fun zenon_H1b=>(zenon_all _p_S1_T (fun y:_p_S1_T=>(
(Is_true (_p_S1_equal (abst_prj_a (abst_constr n1 n2)) y))->(Is_true (
_p_S1_equal y (abst_prj_a (abst_constr n1 n2)))))) n1 (fun zenon_H1a=>(
zenon_imply _ _ (fun zenon_H19=>(zenon_H19 zenon_H18)) (fun zenon_Ha=>(
zenon_Hb zenon_Ha)) zenon_H1a)) zenon_H1b)) _p_S1_equal_symmetric))
zenon_H1c)) abst_prj_a_is_first_of_pair)) zenon_H1d)) in (let zenon_H5
:=(fun zenon_H17=>(zenon_subst _ (fun zenon_Vg=>(Is_true zenon_Vg)) (
_p_S1_equal (abst_prj_a (abst_constr n1 n2)) n3) (_p_S1_equal n1 n3) (
fun zenon_H6=>(zenon_subst _ (fun zenon_Vh=>(~((_p_S1_equal zenon_Vh n3)
 = (_p_S1_equal n1 n3)))) (abst_prj_a (abst_constr n1 n2)) n1 (fun
zenon_H11=>(zenon_notand _ _ (fun zenon_H15=>(zenon_H15 (fun zenon_H13=>
(let zenon_H10:=(fun zenon_H12=>(zenon_subst _ (fun zenon_Vi=>(zenon_Vi
= n1)) n1 (abst_prj_a (abst_constr n1 n2)) (fun zenon_H14=>(zenon_H14
zenon_H13)) zenon_H11 zenon_H12)) in (zenon_noteq _ n1 zenon_H10))))) (
fun zenon_Hf=>(zenon_Hf (fun zenon_Ha=>(zenon_all _p_S1_T (fun x
:_p_S1_T=>(forall y:_p_S1_T,(forall z:_p_S1_T,((Is_true (_p_S1_equal x
y))->((Is_true (_p_S1_equal y z))->(Is_true (_p_S1_equal x z))))))) n1 (
fun zenon_He=>(zenon_all _p_S1_T (fun y:_p_S1_T=>(forall z:_p_S1_T,((
Is_true (_p_S1_equal n1 y))->((Is_true (_p_S1_equal y z))->(Is_true (
_p_S1_equal n1 z)))))) (abst_prj_a (abst_constr n1 n2)) (fun zenon_Hd=>(
zenon_all _p_S1_T (fun z:_p_S1_T=>((Is_true (_p_S1_equal n1 (abst_prj_a
(abst_constr n1 n2))))->((Is_true (_p_S1_equal (abst_prj_a (abst_constr
n1 n2)) z))->(Is_true (_p_S1_equal n1 z))))) n3 (fun zenon_Hc=>(
zenon_imply _ _ (fun zenon_Hb=>(zenon_Hb zenon_Ha)) (fun zenon_H9=>(
zenon_imply _ _ (fun zenon_H8=>(zenon_H8 __B_1_4_LEMMA)) (fun zenon_H7=>
(zenon_G zenon_H7)) zenon_H9)) zenon_Hc)) zenon_Hd)) zenon_He))
_p_S1_equal_transitive)))) zenon_H16)) (zenon_notnot _ (refl_equal (
_p_S1_equal n1 n3))) zenon_H6)) zenon_G __B_1_4_LEMMA)) in (zenon_noteq
_ n3 zenon_H5)))))).
Qed.

        Theorem __B_1_6_LEMMA : Is_true ((_p_S1_equal n1 n3)).
        assert (__force_use_H1 := H1).
        apply for_zenon___B_1_6_LEMMA;
        auto.
        Qed.
        End __B_1_6.
      Section __B_1_7.
(* File "pair.fcl", line 169, characters 4-87 *)
Theorem for_zenon___B_1_7_LEMMA:(Is_true (_p_S2_equal n2 n4)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(let zenon_H16:=(fun zenon_H1d=>(zenon_and _ _ (
fun zenon_H14 zenon_Hb=>(zenon_all _p_S1_T (fun n1:_p_S1_T=>(forall n2
:_p_S2_T,(Is_true (_p_S2_equal (abst_prj_b (abst_constr n1 n2)) n2))))
n1 (fun zenon_H1c=>(zenon_all _p_S2_T (fun n2:_p_S2_T=>(Is_true (
_p_S2_equal (abst_prj_b (abst_constr n1 n2)) n2))) n2 (fun zenon_H18=>(
zenon_all _p_S2_T (fun x:_p_S2_T=>(forall y:_p_S2_T,((Is_true (
_p_S2_equal x y))->(Is_true (_p_S2_equal y x))))) (abst_prj_b (
abst_constr n1 n2)) (fun zenon_H1b=>(zenon_all _p_S2_T (fun y:_p_S2_T=>(
(Is_true (_p_S2_equal (abst_prj_b (abst_constr n1 n2)) y))->(Is_true (
_p_S2_equal y (abst_prj_b (abst_constr n1 n2)))))) n2 (fun zenon_H1a=>(
zenon_imply _ _ (fun zenon_H19=>(zenon_H19 zenon_H18)) (fun zenon_Ha=>(
zenon_Hb zenon_Ha)) zenon_H1a)) zenon_H1b)) _p_S2_equal_symmetric))
zenon_H1c)) abst_prj_b_is_snd_of_pair)) zenon_H1d)) in (let zenon_H5:=(
fun zenon_H17=>(zenon_subst _ (fun zenon_Vf=>(Is_true zenon_Vf)) (
_p_S2_equal (abst_prj_b (abst_constr n1 n2)) n4) (_p_S2_equal n2 n4) (
fun zenon_H6=>(zenon_subst _ (fun zenon_Vg=>(~((_p_S2_equal zenon_Vg n4)
 = (_p_S2_equal n2 n4)))) (abst_prj_b (abst_constr n1 n2)) n2 (fun
zenon_H11=>(zenon_notand _ _ (fun zenon_H15=>(zenon_H15 (fun zenon_H13=>
(let zenon_H10:=(fun zenon_H12=>(zenon_subst _ (fun zenon_Vh=>(zenon_Vh
= n2)) n2 (abst_prj_b (abst_constr n1 n2)) (fun zenon_H14=>(zenon_H14
zenon_H13)) zenon_H11 zenon_H12)) in (zenon_noteq _ n2 zenon_H10))))) (
fun zenon_Hf=>(zenon_Hf (fun zenon_Ha=>(zenon_all _p_S2_T (fun x
:_p_S2_T=>(forall y:_p_S2_T,(forall z:_p_S2_T,((Is_true (_p_S2_equal x
y))->((Is_true (_p_S2_equal y z))->(Is_true (_p_S2_equal x z))))))) n2 (
fun zenon_He=>(zenon_all _p_S2_T (fun y:_p_S2_T=>(forall z:_p_S2_T,((
Is_true (_p_S2_equal n2 y))->((Is_true (_p_S2_equal y z))->(Is_true (
_p_S2_equal n2 z)))))) (abst_prj_b (abst_constr n1 n2)) (fun zenon_Hd=>(
zenon_all _p_S2_T (fun z:_p_S2_T=>((Is_true (_p_S2_equal n2 (abst_prj_b
(abst_constr n1 n2))))->((Is_true (_p_S2_equal (abst_prj_b (abst_constr
n1 n2)) z))->(Is_true (_p_S2_equal n2 z))))) n4 (fun zenon_Hc=>(
zenon_imply _ _ (fun zenon_Hb=>(zenon_Hb zenon_Ha)) (fun zenon_H9=>(
zenon_imply _ _ (fun zenon_H8=>(zenon_H8 __B_1_5_LEMMA)) (fun zenon_H7=>
(zenon_G zenon_H7)) zenon_H9)) zenon_Hc)) zenon_Hd)) zenon_He))
_p_S2_equal_transitive)))) zenon_H16)) (zenon_notnot _ (refl_equal (
_p_S2_equal n2 n4))) zenon_H6)) zenon_G __B_1_5_LEMMA)) in (zenon_noteq
_ n4 zenon_H5)))))).
Qed.

        Theorem __B_1_7_LEMMA : Is_true ((_p_S2_equal n2 n4)).
        assert (__force_use_H1 := H1).
        apply for_zenon___B_1_7_LEMMA;
        auto.
        Qed.
        End __B_1_7.
(* File "pair.fcl", line 171, characters 13-31 *)
Theorem for_zenon___B_1_LEMMA:((Is_true (_p_S1_equal n1 n3))/\(Is_true (
_p_S2_equal n2 n4))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notand _ _ (fun zenon_H4=>(zenon_H4
__B_1_6_LEMMA)) (fun zenon_H3=>(zenon_H3 __B_1_7_LEMMA)) zenon_G)))).
Qed.

      Theorem __B_1_LEMMA :
        (Is_true ((_p_S1_equal n1 n3)) /\ Is_true ((_p_S2_equal n2 n4))).
      assert (__force_use_H1 := H1).
      apply for_zenon___B_1_LEMMA;
      auto.
      Qed.
      End __B_1.
    Section __B_2.
      Variable n1 : _p_S1_T.
      Variable n3 : _p_S1_T.
      Variable n2 : _p_S2_T.
      Variable n4 : _p_S2_T.
      Variable H12 : Is_true ((_p_S1_equal n1 n3)).
      Variable H22 : Is_true ((_p_S2_equal n2 n4)).
      Section __B_2_1.
(* File "pair.fcl", line 183, characters 4-74 *)
Theorem for_zenon___B_2_1_LEMMA:(Is_true (_p_S1_equal (abst_prj_a (
abst_constr n1 n2)) n3)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(let zenon_H15:=(fun zenon_H18=>(zenon_and _ _ (
fun zenon_H13 zenon_Ha=>(zenon_all _p_S1_T (fun n1:_p_S1_T=>(forall n2
:_p_S2_T,(Is_true (_p_S1_equal (abst_prj_a (abst_constr n1 n2)) n1))))
n1 (fun zenon_H17=>(zenon_all _p_S2_T (fun n2:_p_S2_T=>(Is_true (
_p_S1_equal (abst_prj_a (abst_constr n1 n2)) n1))) n2 (fun zenon_H9=>(
zenon_Ha zenon_H9)) zenon_H17)) abst_prj_a_is_first_of_pair)) zenon_H18)
) in (let zenon_H4:=(fun zenon_H16=>(zenon_subst _ (fun zenon_Vg=>(
Is_true zenon_Vg)) (_p_S1_equal n1 n3) (_p_S1_equal (abst_prj_a (
abst_constr n1 n2)) n3) (fun zenon_H5=>(zenon_subst _ (fun zenon_Vh=>(~(
(_p_S1_equal zenon_Vh n3) = (_p_S1_equal (abst_prj_a (abst_constr n1 n2)
) n3)))) n1 (abst_prj_a (abst_constr n1 n2)) (fun zenon_H10=>(
zenon_notand _ _ (fun zenon_H14=>(zenon_H14 (fun zenon_H12=>(let
zenon_Hf:=(fun zenon_H11=>(zenon_subst _ (fun zenon_Vi=>(zenon_Vi = (
abst_prj_a (abst_constr n1 n2)))) (abst_prj_a (abst_constr n1 n2)) n1 (
fun zenon_H13=>(zenon_H13 zenon_H12)) zenon_H10 zenon_H11)) in (
zenon_noteq _ (abst_prj_a (abst_constr n1 n2)) zenon_Hf))))) (fun
zenon_He=>(zenon_He (fun zenon_H9=>(zenon_all _p_S1_T (fun x:_p_S1_T=>(
forall y:_p_S1_T,(forall z:_p_S1_T,((Is_true (_p_S1_equal x y))->((
Is_true (_p_S1_equal y z))->(Is_true (_p_S1_equal x z))))))) (
abst_prj_a (abst_constr n1 n2)) (fun zenon_Hd=>(zenon_all _p_S1_T (fun
y:_p_S1_T=>(forall z:_p_S1_T,((Is_true (_p_S1_equal (abst_prj_a (
abst_constr n1 n2)) y))->((Is_true (_p_S1_equal y z))->(Is_true (
_p_S1_equal (abst_prj_a (abst_constr n1 n2)) z)))))) n1 (fun zenon_Hc=>(
zenon_all _p_S1_T (fun z:_p_S1_T=>((Is_true (_p_S1_equal (abst_prj_a (
abst_constr n1 n2)) n1))->((Is_true (_p_S1_equal n1 z))->(Is_true (
_p_S1_equal (abst_prj_a (abst_constr n1 n2)) z))))) n3 (fun zenon_Hb=>(
zenon_imply _ _ (fun zenon_Ha=>(zenon_Ha zenon_H9)) (fun zenon_H8=>(
zenon_imply _ _ (fun zenon_H7=>(zenon_H7 H12)) (fun zenon_H6=>(zenon_G
zenon_H6)) zenon_H8)) zenon_Hb)) zenon_Hc)) zenon_Hd))
_p_S1_equal_transitive)))) zenon_H15)) (zenon_notnot _ (refl_equal (
_p_S1_equal (abst_prj_a (abst_constr n1 n2)) n3))) zenon_H5)) zenon_G
H12)) in (zenon_noteq _ n3 zenon_H4)))))).
Qed.

        Theorem __B_2_1_LEMMA :
          Is_true ((_p_S1_equal (abst_prj_a (abst_constr n1 n2)) n3)).
        assert (__force_use_H12 := H12).
        assert (__force_use_H22 := H22).
        apply for_zenon___B_2_1_LEMMA;
        auto.
        Qed.
        End __B_2_1.
      Section __B_2_2.
(* File "pair.fcl", line 186, characters 4-73 *)
Theorem for_zenon___B_2_2_LEMMA:(Is_true (_p_S2_equal (abst_prj_b (
abst_constr n1 n2)) n4)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(let zenon_H15:=(fun zenon_H18=>(zenon_and _ _ (
fun zenon_H13 zenon_Ha=>(zenon_all _p_S1_T (fun n1:_p_S1_T=>(forall n2
:_p_S2_T,(Is_true (_p_S2_equal (abst_prj_b (abst_constr n1 n2)) n2))))
n1 (fun zenon_H17=>(zenon_all _p_S2_T (fun n2:_p_S2_T=>(Is_true (
_p_S2_equal (abst_prj_b (abst_constr n1 n2)) n2))) n2 (fun zenon_H9=>(
zenon_Ha zenon_H9)) zenon_H17)) abst_prj_b_is_snd_of_pair)) zenon_H18))
in (let zenon_H4:=(fun zenon_H16=>(zenon_subst _ (fun zenon_Vf=>(
Is_true zenon_Vf)) (_p_S2_equal n2 n4) (_p_S2_equal (abst_prj_b (
abst_constr n1 n2)) n4) (fun zenon_H5=>(zenon_subst _ (fun zenon_Vg=>(~(
(_p_S2_equal zenon_Vg n4) = (_p_S2_equal (abst_prj_b (abst_constr n1 n2)
) n4)))) n2 (abst_prj_b (abst_constr n1 n2)) (fun zenon_H10=>(
zenon_notand _ _ (fun zenon_H14=>(zenon_H14 (fun zenon_H12=>(let
zenon_Hf:=(fun zenon_H11=>(zenon_subst _ (fun zenon_Vh=>(zenon_Vh = (
abst_prj_b (abst_constr n1 n2)))) (abst_prj_b (abst_constr n1 n2)) n2 (
fun zenon_H13=>(zenon_H13 zenon_H12)) zenon_H10 zenon_H11)) in (
zenon_noteq _ (abst_prj_b (abst_constr n1 n2)) zenon_Hf))))) (fun
zenon_He=>(zenon_He (fun zenon_H9=>(zenon_all _p_S2_T (fun x:_p_S2_T=>(
forall y:_p_S2_T,(forall z:_p_S2_T,((Is_true (_p_S2_equal x y))->((
Is_true (_p_S2_equal y z))->(Is_true (_p_S2_equal x z))))))) (
abst_prj_b (abst_constr n1 n2)) (fun zenon_Hd=>(zenon_all _p_S2_T (fun
y:_p_S2_T=>(forall z:_p_S2_T,((Is_true (_p_S2_equal (abst_prj_b (
abst_constr n1 n2)) y))->((Is_true (_p_S2_equal y z))->(Is_true (
_p_S2_equal (abst_prj_b (abst_constr n1 n2)) z)))))) n2 (fun zenon_Hc=>(
zenon_all _p_S2_T (fun z:_p_S2_T=>((Is_true (_p_S2_equal (abst_prj_b (
abst_constr n1 n2)) n2))->((Is_true (_p_S2_equal n2 z))->(Is_true (
_p_S2_equal (abst_prj_b (abst_constr n1 n2)) z))))) n4 (fun zenon_Hb=>(
zenon_imply _ _ (fun zenon_Ha=>(zenon_Ha zenon_H9)) (fun zenon_H8=>(
zenon_imply _ _ (fun zenon_H7=>(zenon_H7 H22)) (fun zenon_H6=>(zenon_G
zenon_H6)) zenon_H8)) zenon_Hb)) zenon_Hc)) zenon_Hd))
_p_S2_equal_transitive)))) zenon_H15)) (zenon_notnot _ (refl_equal (
_p_S2_equal (abst_prj_b (abst_constr n1 n2)) n4))) zenon_H5)) zenon_G
H22)) in (zenon_noteq _ n4 zenon_H4)))))).
Qed.

        Theorem __B_2_2_LEMMA :
          Is_true ((_p_S2_equal (abst_prj_b (abst_constr n1 n2)) n4)).
        assert (__force_use_H12 := H12).
        assert (__force_use_H22 := H22).
        apply for_zenon___B_2_2_LEMMA;
        auto.
        Qed.
        End __B_2_2.
      Section __B_2_3.
(* File "pair.fcl", line 189, character 4, line 190, character 23 *)
Theorem for_zenon___B_2_3_LEMMA:(Is_true (_p_S1_equal (abst_prj_a (
abst_constr n1 n2)) (abst_prj_a (abst_constr n3 n4)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(let zenon_H6:=(fun zenon_H5=>(zenon_all _p_S1_T (
fun x:_p_S1_T=>(forall y:_p_S1_T,(forall z:_p_S1_T,((Is_true (
_p_S1_equal x y))->((Is_true (_p_S1_equal y z))->(Is_true (_p_S1_equal
x z))))))) (abst_prj_a (abst_constr n1 n2)) (fun zenon_H11=>(zenon_all
_p_S1_T (fun y:_p_S1_T=>(forall z:_p_S1_T,((Is_true (_p_S1_equal (
abst_prj_a (abst_constr n1 n2)) y))->((Is_true (_p_S1_equal y z))->(
Is_true (_p_S1_equal (abst_prj_a (abst_constr n1 n2)) z)))))) n3 (fun
zenon_H10=>(zenon_all _p_S1_T (fun z:_p_S1_T=>((Is_true (_p_S1_equal (
abst_prj_a (abst_constr n1 n2)) n3))->((Is_true (_p_S1_equal n3 z))->(
Is_true (_p_S1_equal (abst_prj_a (abst_constr n1 n2)) z))))) (
abst_prj_a (abst_constr n3 n4)) (fun zenon_Hf=>(zenon_imply _ _ (fun
zenon_He=>(zenon_He __B_2_1_LEMMA)) (fun zenon_Hd=>(zenon_imply _ _ (
fun zenon_H6=>(zenon_H6 zenon_H5)) (fun zenon_Hc=>(zenon_G zenon_Hc))
zenon_Hd)) zenon_Hf)) zenon_H10)) zenon_H11)) _p_S1_equal_transitive))
in (zenon_all _p_S1_T (fun n1:_p_S1_T=>(forall n2:_p_S2_T,(Is_true (
_p_S1_equal (abst_prj_a (abst_constr n1 n2)) n1)))) n3 (fun zenon_Hb=>(
zenon_all _p_S2_T (fun n2:_p_S2_T=>(Is_true (_p_S1_equal (abst_prj_a (
abst_constr n3 n2)) n3))) n4 (fun zenon_H7=>(zenon_all _p_S1_T (fun x
:_p_S1_T=>(forall y:_p_S1_T,((Is_true (_p_S1_equal x y))->(Is_true (
_p_S1_equal y x))))) (abst_prj_a (abst_constr n3 n4)) (fun zenon_Ha=>(
zenon_all _p_S1_T (fun y:_p_S1_T=>((Is_true (_p_S1_equal (abst_prj_a (
abst_constr n3 n4)) y))->(Is_true (_p_S1_equal y (abst_prj_a (
abst_constr n3 n4)))))) n3 (fun zenon_H9=>(zenon_imply _ _ (fun
zenon_H8=>(zenon_H8 zenon_H7)) (fun zenon_H5=>(zenon_H6 zenon_H5))
zenon_H9)) zenon_Ha)) _p_S1_equal_symmetric)) zenon_Hb))
abst_prj_a_is_first_of_pair))))).
Qed.

        Theorem __B_2_3_LEMMA :
          Is_true ((_p_S1_equal (abst_prj_a (abst_constr n1 n2))
                     (abst_prj_a (abst_constr n3 n4)))).
        assert (__force_use_H12 := H12).
        assert (__force_use_H22 := H22).
        apply for_zenon___B_2_3_LEMMA;
        auto.
        Qed.
        End __B_2_3.
      Section __B_2_4.
(* File "pair.fcl", line 193, character 4, line 194, character 23 *)
Theorem for_zenon___B_2_4_LEMMA:(Is_true (_p_S2_equal (abst_prj_b (
abst_constr n1 n2)) (abst_prj_b (abst_constr n3 n4)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(let zenon_H6:=(fun zenon_H5=>(zenon_all _p_S2_T (
fun x:_p_S2_T=>(forall y:_p_S2_T,(forall z:_p_S2_T,((Is_true (
_p_S2_equal x y))->((Is_true (_p_S2_equal y z))->(Is_true (_p_S2_equal
x z))))))) (abst_prj_b (abst_constr n1 n2)) (fun zenon_H11=>(zenon_all
_p_S2_T (fun y:_p_S2_T=>(forall z:_p_S2_T,((Is_true (_p_S2_equal (
abst_prj_b (abst_constr n1 n2)) y))->((Is_true (_p_S2_equal y z))->(
Is_true (_p_S2_equal (abst_prj_b (abst_constr n1 n2)) z)))))) n4 (fun
zenon_H10=>(zenon_all _p_S2_T (fun z:_p_S2_T=>((Is_true (_p_S2_equal (
abst_prj_b (abst_constr n1 n2)) n4))->((Is_true (_p_S2_equal n4 z))->(
Is_true (_p_S2_equal (abst_prj_b (abst_constr n1 n2)) z))))) (
abst_prj_b (abst_constr n3 n4)) (fun zenon_Hf=>(zenon_imply _ _ (fun
zenon_He=>(zenon_He __B_2_2_LEMMA)) (fun zenon_Hd=>(zenon_imply _ _ (
fun zenon_H6=>(zenon_H6 zenon_H5)) (fun zenon_Hc=>(zenon_G zenon_Hc))
zenon_Hd)) zenon_Hf)) zenon_H10)) zenon_H11)) _p_S2_equal_transitive))
in (zenon_all _p_S1_T (fun n1:_p_S1_T=>(forall n2:_p_S2_T,(Is_true (
_p_S2_equal (abst_prj_b (abst_constr n1 n2)) n2)))) n3 (fun zenon_Hb=>(
zenon_all _p_S2_T (fun n2:_p_S2_T=>(Is_true (_p_S2_equal (abst_prj_b (
abst_constr n3 n2)) n2))) n4 (fun zenon_H7=>(zenon_all _p_S2_T (fun x
:_p_S2_T=>(forall y:_p_S2_T,((Is_true (_p_S2_equal x y))->(Is_true (
_p_S2_equal y x))))) (abst_prj_b (abst_constr n3 n4)) (fun zenon_Ha=>(
zenon_all _p_S2_T (fun y:_p_S2_T=>((Is_true (_p_S2_equal (abst_prj_b (
abst_constr n3 n4)) y))->(Is_true (_p_S2_equal y (abst_prj_b (
abst_constr n3 n4)))))) n4 (fun zenon_H9=>(zenon_imply _ _ (fun
zenon_H8=>(zenon_H8 zenon_H7)) (fun zenon_H5=>(zenon_H6 zenon_H5))
zenon_H9)) zenon_Ha)) _p_S2_equal_symmetric)) zenon_Hb))
abst_prj_b_is_snd_of_pair))))).
Qed.

        Theorem __B_2_4_LEMMA :
          Is_true ((_p_S2_equal (abst_prj_b (abst_constr n1 n2))
                     (abst_prj_b (abst_constr n3 n4)))).
        assert (__force_use_H12 := H12).
        assert (__force_use_H22 := H22).
        apply for_zenon___B_2_4_LEMMA;
        auto.
        Qed.
        End __B_2_4.
(* File "pair.fcl", line 196, characters 13-50 *)
Theorem for_zenon___B_2_LEMMA:(Is_true (abst_equal (abst_constr n1 n2) (
abst_constr n3 n4))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all abst_T (fun p1:abst_T=>(forall p2
:abst_T,((Is_true (abst_equal p1 p2))<->((Is_true (_p_S1_equal (
abst_prj_a p1) (abst_prj_a p2)))/\(Is_true (_p_S2_equal (abst_prj_b p1)
(abst_prj_b p2))))))) (abst_constr n1 n2) (fun zenon_Ha=>(zenon_all
abst_T (fun p2:abst_T=>((Is_true (abst_equal (abst_constr n1 n2) p2))<->
((Is_true (_p_S1_equal (abst_prj_a (abst_constr n1 n2)) (abst_prj_a p2))
)/\(Is_true (_p_S2_equal (abst_prj_b (abst_constr n1 n2)) (abst_prj_b
p2)))))) (abst_constr n3 n4) (fun zenon_H9=>(zenon_equiv _ _ (fun
zenon_G zenon_H7=>(zenon_notand _ _ (fun zenon_H6=>(zenon_H6
__B_2_3_LEMMA)) (fun zenon_H5=>(zenon_H5 __B_2_4_LEMMA)) zenon_H7)) (
fun zenon_H4 zenon_H8=>(zenon_G zenon_H4)) zenon_H9)) zenon_Ha))
abst_def_equal)))).
Qed.

      Theorem __B_2_LEMMA :
        Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))).
      assert (__force_use_H12 := H12).
      assert (__force_use_H22 := H22).
      apply for_zenon___B_2_LEMMA;
      auto.
      Qed.
      End __B_2.
(* File "pair.fcl", line 198, characters 2-15 *)
Theorem for_zenon_def_equal1:(forall n1:_p_S1_T,(forall n3:_p_S1_T,(
forall n2:_p_S2_T,(forall n4:_p_S2_T,((Is_true (abst_equal (abst_constr
n1 n2) (abst_constr n3 n4)))<->((Is_true (_p_S1_equal n1 n3))/\(Is_true
(_p_S2_equal n2 n4)))))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun n1:_p_S1_T=>(forall n3
:_p_S1_T,(forall n2:_p_S2_T,(forall n4:_p_S2_T,((Is_true (abst_equal (
abst_constr n1 n2) (abst_constr n3 n4)))<->((Is_true (_p_S1_equal n1 n3)
)/\(Is_true (_p_S2_equal n2 n4)))))))) (fun zenon_H1f=>(zenon_ex
_p_S1_T (fun n1:_p_S1_T=>(~(forall n3:_p_S1_T,(forall n2:_p_S2_T,(
forall n4:_p_S2_T,((Is_true (abst_equal (abst_constr n1 n2) (
abst_constr n3 n4)))<->((Is_true (_p_S1_equal n1 n3))/\(Is_true (
_p_S2_equal n2 n4))))))))) (fun(zenon_Tn1_d:_p_S1_T) zenon_H1e=>(
zenon_notallex (fun n3:_p_S1_T=>(forall n2:_p_S2_T,(forall n4:_p_S2_T,((
Is_true (abst_equal (abst_constr zenon_Tn1_d n2) (abst_constr n3 n4)))
<->((Is_true (_p_S1_equal zenon_Tn1_d n3))/\(Is_true (_p_S2_equal n2 n4)
)))))) (fun zenon_H1d=>(zenon_ex _p_S1_T (fun n3:_p_S1_T=>(~(forall n2
:_p_S2_T,(forall n4:_p_S2_T,((Is_true (abst_equal (abst_constr
zenon_Tn1_d n2) (abst_constr n3 n4)))<->((Is_true (_p_S1_equal
zenon_Tn1_d n3))/\(Is_true (_p_S2_equal n2 n4)))))))) (fun(zenon_Tn3_e
:_p_S1_T) zenon_H1c=>(zenon_notallex (fun n2:_p_S2_T=>(forall n4
:_p_S2_T,((Is_true (abst_equal (abst_constr zenon_Tn1_d n2) (
abst_constr zenon_Tn3_e n4)))<->((Is_true (_p_S1_equal zenon_Tn1_d
zenon_Tn3_e))/\(Is_true (_p_S2_equal n2 n4)))))) (fun zenon_H1b=>(
zenon_ex _p_S2_T (fun n2:_p_S2_T=>(~(forall n4:_p_S2_T,((Is_true (
abst_equal (abst_constr zenon_Tn1_d n2) (abst_constr zenon_Tn3_e n4)))
<->((Is_true (_p_S1_equal zenon_Tn1_d zenon_Tn3_e))/\(Is_true (
_p_S2_equal n2 n4))))))) (fun(zenon_Tn2_f:_p_S2_T) zenon_H1a=>(
zenon_notallex (fun n4:_p_S2_T=>((Is_true (abst_equal (abst_constr
zenon_Tn1_d zenon_Tn2_f) (abst_constr zenon_Tn3_e n4)))<->((Is_true (
_p_S1_equal zenon_Tn1_d zenon_Tn3_e))/\(Is_true (_p_S2_equal
zenon_Tn2_f n4))))) (fun zenon_H19=>(zenon_ex _p_S2_T (fun n4:_p_S2_T=>(
~((Is_true (abst_equal (abst_constr zenon_Tn1_d zenon_Tn2_f) (
abst_constr zenon_Tn3_e n4)))<->((Is_true (_p_S1_equal zenon_Tn1_d
zenon_Tn3_e))/\(Is_true (_p_S2_equal zenon_Tn2_f n4)))))) (fun(
zenon_Tn4_m:_p_S2_T) zenon_H18=>(zenon_notequiv _ _ (fun zenon_H9
zenon_H6=>(zenon_and _ _ (fun zenon_H12 zenon_Hf=>(zenon_all _p_S1_T (
fun n1:_p_S1_T=>(forall n3:_p_S1_T,(forall n2:_p_S2_T,(forall n4
:_p_S2_T,((Is_true (_p_S1_equal n1 n3))->((Is_true (_p_S2_equal n2 n4))
->(Is_true (abst_equal (abst_constr n1 n2) (abst_constr n3 n4)))))))))
zenon_Tn1_d (fun zenon_H17=>(zenon_all _p_S1_T (fun n3:_p_S1_T=>(forall
n2:_p_S2_T,(forall n4:_p_S2_T,((Is_true (_p_S1_equal zenon_Tn1_d n3))->(
(Is_true (_p_S2_equal n2 n4))->(Is_true (abst_equal (abst_constr
zenon_Tn1_d n2) (abst_constr n3 n4)))))))) zenon_Tn3_e (fun zenon_H16=>(
zenon_all _p_S2_T (fun n2:_p_S2_T=>(forall n4:_p_S2_T,((Is_true (
_p_S1_equal zenon_Tn1_d zenon_Tn3_e))->((Is_true (_p_S2_equal n2 n4))->(
Is_true (abst_equal (abst_constr zenon_Tn1_d n2) (abst_constr
zenon_Tn3_e n4))))))) zenon_Tn2_f (fun zenon_H15=>(zenon_all _p_S2_T (
fun n4:_p_S2_T=>((Is_true (_p_S1_equal zenon_Tn1_d zenon_Tn3_e))->((
Is_true (_p_S2_equal zenon_Tn2_f n4))->(Is_true (abst_equal (
abst_constr zenon_Tn1_d zenon_Tn2_f) (abst_constr zenon_Tn3_e n4))))))
zenon_Tn4_m (fun zenon_H14=>(zenon_imply _ _ (fun zenon_H13=>(zenon_H13
zenon_H12)) (fun zenon_H11=>(zenon_imply _ _ (fun zenon_H10=>(zenon_H10
zenon_Hf)) (fun zenon_H8=>(zenon_H9 zenon_H8)) zenon_H11)) zenon_H14))
zenon_H15)) zenon_H16)) zenon_H17)) __B_2_LEMMA)) zenon_H6)) (fun
zenon_H8 zenon_H7=>(zenon_all _p_S1_T (fun n1:_p_S1_T=>(forall n3
:_p_S1_T,(forall n2:_p_S2_T,(forall n4:_p_S2_T,((Is_true (abst_equal (
abst_constr n1 n2) (abst_constr n3 n4)))->((Is_true (_p_S1_equal n1 n3))
/\(Is_true (_p_S2_equal n2 n4)))))))) zenon_Tn1_d (fun zenon_He=>(
zenon_all _p_S1_T (fun n3:_p_S1_T=>(forall n2:_p_S2_T,(forall n4
:_p_S2_T,((Is_true (abst_equal (abst_constr zenon_Tn1_d n2) (
abst_constr n3 n4)))->((Is_true (_p_S1_equal zenon_Tn1_d n3))/\(Is_true
(_p_S2_equal n2 n4))))))) zenon_Tn3_e (fun zenon_Hd=>(zenon_all _p_S2_T
(fun n2:_p_S2_T=>(forall n4:_p_S2_T,((Is_true (abst_equal (abst_constr
zenon_Tn1_d n2) (abst_constr zenon_Tn3_e n4)))->((Is_true (_p_S1_equal
zenon_Tn1_d zenon_Tn3_e))/\(Is_true (_p_S2_equal n2 n4))))))
zenon_Tn2_f (fun zenon_Hb=>(zenon_all _p_S2_T (fun n4:_p_S2_T=>((
Is_true (abst_equal (abst_constr zenon_Tn1_d zenon_Tn2_f) (abst_constr
zenon_Tn3_e n4)))->((Is_true (_p_S1_equal zenon_Tn1_d zenon_Tn3_e))/\(
Is_true (_p_S2_equal zenon_Tn2_f n4))))) zenon_Tn4_m (fun zenon_Ha=>(
zenon_imply _ _ (fun zenon_H9=>(zenon_H9 zenon_H8)) (fun zenon_H6=>(
zenon_H7 zenon_H6)) zenon_Ha)) zenon_Hb)) zenon_Hd)) zenon_He))
__B_1_LEMMA)) zenon_H18)) zenon_H19)) zenon_H1a)) zenon_H1b)) zenon_H1c)
) zenon_H1d)) zenon_H1e)) zenon_H1f)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_def_equal1 :
      forall n1  n3 : _p_S1_T,
        forall n2  n4 : _p_S2_T,
          Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))) <->
            (Is_true ((_p_S1_equal n1 n3)) /\ Is_true ((_p_S2_equal n2 n4))).
    assert (__force_use_p_S1_T := _p_S1_T).
    assert (__force_use_p_S2_T := _p_S2_T).
    assert (__force_use__p_S1_equal := _p_S1_equal).
    assert (__force_use__p_S1_equal_symmetric := _p_S1_equal_symmetric).
    assert (__force_use__p_S1_equal_transitive := _p_S1_equal_transitive).
    assert (__force_use__p_S2_equal := _p_S2_equal).
    assert (__force_use__p_S2_equal_symmetric := _p_S2_equal_symmetric).
    assert (__force_use__p_S2_equal_transitive := _p_S2_equal_transitive).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_constr := abst_constr).
    assert (__force_use_abst_equal := abst_equal).
    assert (__force_use_abst_prj_a := abst_prj_a).
    assert (__force_use_abst_prj_b := abst_prj_b).
    assert (__force_use_abst_prj_a_is_first_of_pair :=
      abst_prj_a_is_first_of_pair).
    assert (__force_use_abst_def_equal := abst_def_equal).
    assert (__force_use_abst_prj_b_is_snd_of_pair :=
      abst_prj_b_is_snd_of_pair).
    apply for_zenon_def_equal1;
    auto.
    Qed.
    End Proof_of_def_equal1.
  
  Theorem def_equal1  (_p_S1_T : Set) (_p_S2_T : Set) (_p_S1_equal :
    _p_S1_T -> _p_S1_T -> basics.bool__t) (_p_S1_equal_symmetric :
    forall x  y : _p_S1_T,
      Is_true ((_p_S1_equal x y)) -> Is_true ((_p_S1_equal y x)))
    (_p_S1_equal_transitive :
    forall x  y  z : _p_S1_T,
      Is_true ((_p_S1_equal x y)) ->
        Is_true ((_p_S1_equal y z)) -> Is_true ((_p_S1_equal x z)))
    (_p_S2_equal : _p_S2_T -> _p_S2_T -> basics.bool__t)
    (_p_S2_equal_symmetric :
    forall x  y : _p_S2_T,
      Is_true ((_p_S2_equal x y)) -> Is_true ((_p_S2_equal y x)))
    (_p_S2_equal_transitive :
    forall x  y  z : _p_S2_T,
      Is_true ((_p_S2_equal x y)) ->
        Is_true ((_p_S2_equal y z)) -> Is_true ((_p_S2_equal x z)))
    (abst_T : Set) (abst_constr : _p_S1_T -> _p_S2_T -> abst_T)
    (abst_equal : abst_T -> abst_T -> basics.bool__t)
    (abst_prj_a : abst_T -> _p_S1_T) (abst_prj_b : abst_T -> _p_S2_T)
    (abst_prj_a_is_first_of_pair :
    forall n1 : _p_S1_T,
      forall n2 : _p_S2_T,
        Is_true ((_p_S1_equal (abst_prj_a (abst_constr n1 n2)) n1)))
    (abst_def_equal :
    forall p1  p2 : abst_T,
      Is_true ((abst_equal p1 p2)) <->
        (Is_true ((_p_S1_equal (abst_prj_a p1) (abst_prj_a p2))) /\
           Is_true ((_p_S2_equal (abst_prj_b p1) (abst_prj_b p2)))))
    (abst_prj_b_is_snd_of_pair :
    forall n1 : _p_S1_T,
      forall n2 : _p_S2_T,
        Is_true ((_p_S2_equal (abst_prj_b (abst_constr n1 n2)) n2))):
    forall n1  n3 : _p_S1_T,
      forall n2  n4 : _p_S2_T,
        Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))) <->
          (Is_true ((_p_S1_equal n1 n3)) /\ Is_true ((_p_S2_equal n2 n4))).
  apply for_zenon_abstracted_def_equal1;
  auto.
  Qed.
  
  (* From species pair#Imp_pair. *)
  (* Section for proof of theorem 'equal_reflexive'. *)
  Section Proof_of_equal_reflexive.
    Variable _p_S1_T : Set.
    Variable _p_S2_T : Set.
    Variable abst_T : Set.
    Variable abst_constr : _p_S1_T -> _p_S2_T -> abst_T.
    Variable abst_equal : abst_T -> abst_T -> basics.bool__t.
    Variable abst_prj_a : abst_T -> _p_S1_T.
    Variable abst_prj_b : abst_T -> _p_S2_T.
    Hypothesis abst_unicite_1 :
      forall a : abst_T,
        Is_true ((abst_equal (abst_constr (abst_prj_a a) (abst_prj_b a)) a)).
    Hypothesis abst_unicite_2 :
      forall a : abst_T,
        Is_true ((abst_equal a (abst_constr (abst_prj_a a) (abst_prj_b a)))).
    Hypothesis abst_equal_transitive :
      forall x  y  z : abst_T,
        Is_true ((abst_equal x y)) ->
          Is_true ((abst_equal y z)) -> Is_true ((abst_equal x z)).
    Section __C_1.
      Variable p : abst_T.
      Section __C_1_1.
(* File "pair.fcl", line 208, characters 7-28 *)
Theorem for_zenon___C_1_1_LEMMA:(Is_true (abst_equal p (abst_constr (
abst_prj_a p) (abst_prj_b p)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all abst_T (fun a:abst_T=>(Is_true (
abst_equal a (abst_constr (abst_prj_a a) (abst_prj_b a))))) p (fun
zenon_H2=>(zenon_G zenon_H2)) abst_unicite_2)))).
Qed.

        Theorem __C_1_1_LEMMA :
          Is_true ((abst_equal p (abst_constr (abst_prj_a p) (abst_prj_b p)))).
        apply for_zenon___C_1_1_LEMMA;
        auto.
        Qed.
        End __C_1_1.
(* File "pair.fcl", line 210, characters 14-63 *)
Theorem for_zenon___C_1_LEMMA:(Is_true (abst_equal p p)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(let zenon_H5:=(fun zenon_H4=>(zenon_all abst_T (
fun x:abst_T=>(forall y:abst_T,(forall z:abst_T,((Is_true (abst_equal x
y))->((Is_true (abst_equal y z))->(Is_true (abst_equal x z))))))) p (
fun zenon_Hb=>(zenon_all abst_T (fun y:abst_T=>(forall z:abst_T,((
Is_true (abst_equal p y))->((Is_true (abst_equal y z))->(Is_true (
abst_equal p z)))))) (abst_constr (abst_prj_a p) (abst_prj_b p)) (fun
zenon_Ha=>(zenon_all abst_T (fun z:abst_T=>((Is_true (abst_equal p (
abst_constr (abst_prj_a p) (abst_prj_b p))))->((Is_true (abst_equal (
abst_constr (abst_prj_a p) (abst_prj_b p)) z))->(Is_true (abst_equal p
z))))) p (fun zenon_H9=>(zenon_imply _ _ (fun zenon_H8=>(zenon_H8
__C_1_1_LEMMA)) (fun zenon_H7=>(zenon_imply _ _ (fun zenon_H5=>(
zenon_H5 zenon_H4)) (fun zenon_H6=>(zenon_G zenon_H6)) zenon_H7))
zenon_H9)) zenon_Ha)) zenon_Hb)) abst_equal_transitive)) in (zenon_all
abst_T (fun a:abst_T=>(Is_true (abst_equal (abst_constr (abst_prj_a a) (
abst_prj_b a)) a))) p (fun zenon_H4=>(zenon_H5 zenon_H4))
abst_unicite_1))))).
Qed.

      Theorem __C_1_LEMMA : Is_true ((abst_equal p p)).
      apply for_zenon___C_1_LEMMA;
      auto.
      Qed.
      End __C_1.
(* File "pair.fcl", line 212, characters 2-15 *)
Theorem for_zenon_equal_reflexive:(forall p:abst_T,(Is_true (abst_equal
p p))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G __C_1_LEMMA)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_reflexive :
      forall x : abst_T, Is_true ((abst_equal x x)).
    assert (__force_use_p_S1_T := _p_S1_T).
    assert (__force_use_p_S2_T := _p_S2_T).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_constr := abst_constr).
    assert (__force_use_abst_equal := abst_equal).
    assert (__force_use_abst_prj_a := abst_prj_a).
    assert (__force_use_abst_prj_b := abst_prj_b).
    assert (__force_use_abst_unicite_1 := abst_unicite_1).
    assert (__force_use_abst_unicite_2 := abst_unicite_2).
    assert (__force_use_abst_equal_transitive := abst_equal_transitive).
    apply for_zenon_equal_reflexive;
    auto.
    Qed.
    End Proof_of_equal_reflexive.
  
  Theorem equal_reflexive  (_p_S1_T : Set) (_p_S2_T : Set) (abst_T : Set)
    (abst_constr : _p_S1_T -> _p_S2_T -> abst_T)
    (abst_equal : abst_T -> abst_T -> basics.bool__t)
    (abst_prj_a : abst_T -> _p_S1_T) (abst_prj_b : abst_T -> _p_S2_T)
    (abst_unicite_1 :
    forall a : abst_T,
      Is_true ((abst_equal (abst_constr (abst_prj_a a) (abst_prj_b a)) a)))
    (abst_unicite_2 :
    forall a : abst_T,
      Is_true ((abst_equal a (abst_constr (abst_prj_a a) (abst_prj_b a)))))
    (abst_equal_transitive :
    forall x  y  z : abst_T,
      Is_true ((abst_equal x y)) ->
        Is_true ((abst_equal y z)) -> Is_true ((abst_equal x z))):
    forall x : abst_T, Is_true ((abst_equal x x)).
  apply for_zenon_abstracted_equal_reflexive;
  auto.
  Qed.
  
  (* From species pair#Imp_pair. *)
  (* Section for proof of theorem 'equal_reflexive2'. *)
  Section Proof_of_equal_reflexive2.
    Variable _p_S1_T : Set.
    Variable _p_S2_T : Set.
    Variable _p_S1_equal : _p_S1_T -> _p_S1_T -> basics.bool__t.
    Variable _p_S1_equal_reflexive :
      forall x : _p_S1_T, Is_true ((_p_S1_equal x x)).
    Variable _p_S2_equal : _p_S2_T -> _p_S2_T -> basics.bool__t.
    Variable _p_S2_equal_reflexive :
      forall x : _p_S2_T, Is_true ((_p_S2_equal x x)).
    Variable abst_T : Set.
    Variable abst_constr : _p_S1_T -> _p_S2_T -> abst_T.
    Variable abst_equal : abst_T -> abst_T -> basics.bool__t.
    Hypothesis abst_def_equal1 :
      forall n1  n3 : _p_S1_T,
        forall n2  n4 : _p_S2_T,
          Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))) <->
            (Is_true ((_p_S1_equal n1 n3)) /\ Is_true ((_p_S2_equal n2 n4))).
(* File "pair.fcl", line 216, characters 2-64 *)
Theorem for_zenon_equal_reflexive2:(forall n1:_p_S1_T,(forall n2
:_p_S2_T,(Is_true (abst_equal (abst_constr n1 n2) (abst_constr n1 n2))))
).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun n1:_p_S1_T=>(forall n2
:_p_S2_T,(Is_true (abst_equal (abst_constr n1 n2) (abst_constr n1 n2))))
) (fun zenon_H14=>(zenon_ex _p_S1_T (fun n1:_p_S1_T=>(~(forall n2
:_p_S2_T,(Is_true (abst_equal (abst_constr n1 n2) (abst_constr n1 n2))))
)) (fun(zenon_Tn1_e:_p_S1_T) zenon_H13=>(zenon_notallex (fun n2
:_p_S2_T=>(Is_true (abst_equal (abst_constr zenon_Tn1_e n2) (
abst_constr zenon_Tn1_e n2)))) (fun zenon_H12=>(zenon_ex _p_S2_T (fun
n2:_p_S2_T=>(~(Is_true (abst_equal (abst_constr zenon_Tn1_e n2) (
abst_constr zenon_Tn1_e n2))))) (fun(zenon_Tn2_j:_p_S2_T) zenon_H6=>(
zenon_all _p_S1_T (fun n1:_p_S1_T=>(forall n3:_p_S1_T,(forall n2
:_p_S2_T,(forall n4:_p_S2_T,((Is_true (abst_equal (abst_constr n1 n2) (
abst_constr n3 n4)))<->((Is_true (_p_S1_equal n1 n3))/\(Is_true (
_p_S2_equal n2 n4)))))))) zenon_Tn1_e (fun zenon_H11=>(zenon_all
_p_S1_T (fun n3:_p_S1_T=>(forall n2:_p_S2_T,(forall n4:_p_S2_T,((
Is_true (abst_equal (abst_constr zenon_Tn1_e n2) (abst_constr n3 n4)))
<->((Is_true (_p_S1_equal zenon_Tn1_e n3))/\(Is_true (_p_S2_equal n2 n4)
)))))) zenon_Tn1_e (fun zenon_H10=>(zenon_all _p_S2_T (fun n2:_p_S2_T=>(
forall n4:_p_S2_T,((Is_true (abst_equal (abst_constr zenon_Tn1_e n2) (
abst_constr zenon_Tn1_e n4)))<->((Is_true (_p_S1_equal zenon_Tn1_e
zenon_Tn1_e))/\(Is_true (_p_S2_equal n2 n4)))))) zenon_Tn2_j (fun
zenon_Hf=>(zenon_all _p_S2_T (fun n4:_p_S2_T=>((Is_true (abst_equal (
abst_constr zenon_Tn1_e zenon_Tn2_j) (abst_constr zenon_Tn1_e n4)))<->((
Is_true (_p_S1_equal zenon_Tn1_e zenon_Tn1_e))/\(Is_true (_p_S2_equal
zenon_Tn2_j n4))))) zenon_Tn2_j (fun zenon_He=>(zenon_equiv _ _ (fun
zenon_H6 zenon_Hc=>(zenon_notand _ _ (fun zenon_Hb=>(zenon_all _p_S1_T (
fun x:_p_S1_T=>(Is_true (_p_S1_equal x x))) zenon_Tn1_e (fun zenon_Ha=>(
zenon_Hb zenon_Ha)) _p_S1_equal_reflexive)) (fun zenon_H8=>(zenon_all
_p_S2_T (fun x:_p_S2_T=>(Is_true (_p_S2_equal x x))) zenon_Tn2_j (fun
zenon_H7=>(zenon_H8 zenon_H7)) _p_S2_equal_reflexive)) zenon_Hc)) (fun
zenon_H5 zenon_Hd=>(zenon_H6 zenon_H5)) zenon_He)) zenon_Hf)) zenon_H10)
) zenon_H11)) abst_def_equal1)) zenon_H12)) zenon_H13)) zenon_H14))
zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_reflexive2 :
      forall n1 : _p_S1_T,
        forall n2 : _p_S2_T,
          Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n1 n2))).
    assert (__force_use_p_S1_T := _p_S1_T).
    assert (__force_use_p_S2_T := _p_S2_T).
    assert (__force_use__p_S1_equal := _p_S1_equal).
    assert (__force_use__p_S1_equal_reflexive := _p_S1_equal_reflexive).
    assert (__force_use__p_S2_equal := _p_S2_equal).
    assert (__force_use__p_S2_equal_reflexive := _p_S2_equal_reflexive).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_constr := abst_constr).
    assert (__force_use_abst_equal := abst_equal).
    assert (__force_use_abst_def_equal1 := abst_def_equal1).
    apply for_zenon_equal_reflexive2;
    auto.
    Qed.
    End Proof_of_equal_reflexive2.
  
  Theorem equal_reflexive2  (_p_S1_T : Set) (_p_S2_T : Set) (_p_S1_equal :
    _p_S1_T -> _p_S1_T -> basics.bool__t) (_p_S1_equal_reflexive :
    forall x : _p_S1_T, Is_true ((_p_S1_equal x x))) (_p_S2_equal :
    _p_S2_T -> _p_S2_T -> basics.bool__t) (_p_S2_equal_reflexive :
    forall x : _p_S2_T, Is_true ((_p_S2_equal x x))) (abst_T : Set)
    (abst_constr : _p_S1_T -> _p_S2_T -> abst_T)
    (abst_equal : abst_T -> abst_T -> basics.bool__t) (abst_def_equal1 :
    forall n1  n3 : _p_S1_T,
      forall n2  n4 : _p_S2_T,
        Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))) <->
          (Is_true ((_p_S1_equal n1 n3)) /\ Is_true ((_p_S2_equal n2 n4)))):
    forall n1 : _p_S1_T,
      forall n2 : _p_S2_T,
        Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n1 n2))).
  apply for_zenon_abstracted_equal_reflexive2;
  auto.
  Qed.
  
  (* From species pair#Imp_pair. *)
  (* Section for proof of theorem 'equal_symmetric2'. *)
  Section Proof_of_equal_symmetric2.
    Variable _p_S1_T : Set.
    Variable _p_S2_T : Set.
    Variable _p_S1_equal : _p_S1_T -> _p_S1_T -> basics.bool__t.
    Variable _p_S1_equal_symmetric :
      forall x  y : _p_S1_T,
        Is_true ((_p_S1_equal x y)) -> Is_true ((_p_S1_equal y x)).
    Variable _p_S2_equal : _p_S2_T -> _p_S2_T -> basics.bool__t.
    Variable _p_S2_equal_symmetric :
      forall x  y : _p_S2_T,
        Is_true ((_p_S2_equal x y)) -> Is_true ((_p_S2_equal y x)).
    Variable abst_T : Set.
    Variable abst_constr : _p_S1_T -> _p_S2_T -> abst_T.
    Variable abst_equal : abst_T -> abst_T -> basics.bool__t.
    Hypothesis abst_def_equal1 :
      forall n1  n3 : _p_S1_T,
        forall n2  n4 : _p_S2_T,
          Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))) <->
            (Is_true ((_p_S1_equal n1 n3)) /\ Is_true ((_p_S2_equal n2 n4))).
    Section __E_1.
      Variable n1 : _p_S1_T.
      Variable n3 : _p_S1_T.
      Variable n2 : _p_S2_T.
      Variable n4 : _p_S2_T.
      Variable H1 :
        Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))).
      Section __E_1_1.
(* File "pair.fcl", line 256, characters 4-40 *)
Theorem for_zenon___E_1_1_LEMMA:((Is_true (_p_S1_equal n1 n3))/\(
Is_true (_p_S2_equal n2 n4))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_S1_T (fun n1:_p_S1_T=>(forall n3
:_p_S1_T,(forall n2:_p_S2_T,(forall n4:_p_S2_T,((Is_true (abst_equal (
abst_constr n1 n2) (abst_constr n3 n4)))<->((Is_true (_p_S1_equal n1 n3)
)/\(Is_true (_p_S2_equal n2 n4)))))))) n1 (fun zenon_H8=>(zenon_all
_p_S1_T (fun n3:_p_S1_T=>(forall n2:_p_S2_T,(forall n4:_p_S2_T,((
Is_true (abst_equal (abst_constr n1 n2) (abst_constr n3 n4)))<->((
Is_true (_p_S1_equal n1 n3))/\(Is_true (_p_S2_equal n2 n4))))))) n3 (
fun zenon_H7=>(zenon_all _p_S2_T (fun n2:_p_S2_T=>(forall n4:_p_S2_T,((
Is_true (abst_equal (abst_constr n1 n2) (abst_constr n3 n4)))<->((
Is_true (_p_S1_equal n1 n3))/\(Is_true (_p_S2_equal n2 n4)))))) n2 (fun
zenon_H6=>(zenon_all _p_S2_T (fun n4:_p_S2_T=>((Is_true (abst_equal (
abst_constr n1 n2) (abst_constr n3 n4)))<->((Is_true (_p_S1_equal n1 n3)
)/\(Is_true (_p_S2_equal n2 n4))))) n4 (fun zenon_H5=>(zenon_equiv _ _ (
fun zenon_H4 zenon_G=>(zenon_H4 H1)) (fun H1 zenon_H3=>(zenon_G
zenon_H3)) zenon_H5)) zenon_H6)) zenon_H7)) zenon_H8)) abst_def_equal1))
)).
Qed.

        Theorem __E_1_1_LEMMA :
          (Is_true ((_p_S1_equal n1 n3)) /\ Is_true ((_p_S2_equal n2 n4))).
        assert (__force_use_H1 := H1).
        apply for_zenon___E_1_1_LEMMA;
        auto.
        Qed.
        End __E_1_1.
      Section __E_1_2.
(* File "pair.fcl", line 260, characters 6-56 *)
Theorem for_zenon___E_1_2_LEMMA:(((Is_true (_p_S1_equal n1 n3))/\(
Is_true (_p_S2_equal n2 n4)))->((Is_true (_p_S1_equal n3 n1))/\(Is_true
(_p_S2_equal n4 n2)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notimply _ _ (fun zenon_H10 zenon_Hf=>(
zenon_and _ _ (fun zenon_Hb zenon_H5=>(zenon_notand _ _ (fun zenon_Ha=>(
zenon_all _p_S1_T (fun x:_p_S1_T=>(forall y:_p_S1_T,((Is_true (
_p_S1_equal x y))->(Is_true (_p_S1_equal y x))))) n1 (fun zenon_He=>(
zenon_all _p_S1_T (fun y:_p_S1_T=>((Is_true (_p_S1_equal n1 y))->(
Is_true (_p_S1_equal y n1)))) n3 (fun zenon_Hd=>(zenon_imply _ _ (fun
zenon_Hc=>(zenon_Hc zenon_Hb)) (fun zenon_H9=>(zenon_Ha zenon_H9))
zenon_Hd)) zenon_He)) _p_S1_equal_symmetric)) (fun zenon_H4=>(zenon_all
_p_S2_T (fun x:_p_S2_T=>(forall y:_p_S2_T,((Is_true (_p_S2_equal x y))->
(Is_true (_p_S2_equal y x))))) n2 (fun zenon_H8=>(zenon_all _p_S2_T (
fun y:_p_S2_T=>((Is_true (_p_S2_equal n2 y))->(Is_true (_p_S2_equal y
n2)))) n4 (fun zenon_H7=>(zenon_imply _ _ (fun zenon_H6=>(zenon_H6
zenon_H5)) (fun zenon_H3=>(zenon_H4 zenon_H3)) zenon_H7)) zenon_H8))
_p_S2_equal_symmetric)) zenon_Hf)) zenon_H10)) zenon_G)))).
Qed.

        Theorem __E_1_2_LEMMA :
          (Is_true ((_p_S1_equal n1 n3)) /\ Is_true ((_p_S2_equal n2 n4))) ->
            (Is_true ((_p_S1_equal n3 n1)) /\ Is_true ((_p_S2_equal n4 n2))).
        assert (__force_use_H1 := H1).
        apply for_zenon___E_1_2_LEMMA;
        auto.
        Qed.
        End __E_1_2.
      Section __E_1_3.
(* File "pair.fcl", line 264, characters 4-26 *)
Theorem for_zenon___E_1_3_LEMMA:(((Is_true (_p_S1_equal n3 n1))/\(
Is_true (_p_S2_equal n4 n2)))->(Is_true (abst_equal (abst_constr n3 n4)
(abst_constr n1 n2)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notimply _ _ (fun zenon_H9 zenon_H3=>(
zenon_and _ _ (fun zenon_H6 zenon_H4=>(zenon_all _p_S1_T (fun n1
:_p_S1_T=>(forall n3:_p_S1_T,(forall n2:_p_S2_T,(forall n4:_p_S2_T,((
Is_true (abst_equal (abst_constr n1 n2) (abst_constr n3 n4)))<->((
Is_true (_p_S1_equal n1 n3))/\(Is_true (_p_S2_equal n2 n4)))))))) n3 (
fun zenon_Hd=>(zenon_all _p_S1_T (fun zenon_Vg:_p_S1_T=>(forall n2
:_p_S2_T,(forall n4:_p_S2_T,((Is_true (abst_equal (abst_constr n3 n2) (
abst_constr zenon_Vg n4)))<->((Is_true (_p_S1_equal n3 zenon_Vg))/\(
Is_true (_p_S2_equal n2 n4))))))) n1 (fun zenon_Hc=>(zenon_all _p_S2_T (
fun n2:_p_S2_T=>(forall n4:_p_S2_T,((Is_true (abst_equal (abst_constr
n3 n2) (abst_constr n1 n4)))<->((Is_true (_p_S1_equal n3 n1))/\(Is_true
(_p_S2_equal n2 n4)))))) n4 (fun zenon_Hb=>(zenon_all _p_S2_T (fun
zenon_Vh:_p_S2_T=>((Is_true (abst_equal (abst_constr n3 n4) (
abst_constr n1 zenon_Vh)))<->((Is_true (_p_S1_equal n3 n1))/\(Is_true (
_p_S2_equal n4 zenon_Vh))))) n2 (fun zenon_Ha=>(zenon_equiv _ _ (fun
zenon_H3 zenon_H8=>(zenon_notand _ _ (fun zenon_H7=>(zenon_H7 zenon_H6))
 (fun zenon_H5=>(zenon_H5 zenon_H4)) zenon_H8)) (fun zenon_H2 zenon_H9=>
(zenon_H3 zenon_H2)) zenon_Ha)) zenon_Hb)) zenon_Hc)) zenon_Hd))
abst_def_equal1)) zenon_H9)) zenon_G)))).
Qed.

        Theorem __E_1_3_LEMMA :
          (Is_true ((_p_S1_equal n3 n1)) /\ Is_true ((_p_S2_equal n4 n2))) ->
            Is_true ((abst_equal (abst_constr n3 n4) (abst_constr n1 n2))).
        assert (__force_use_H1 := H1).
        apply for_zenon___E_1_3_LEMMA;
        auto.
        Qed.
        End __E_1_3.
(* File "pair.fcl", line 266, characters 13-51 *)
Theorem for_zenon___E_1_LEMMA:(Is_true (abst_equal (abst_constr n3 n4) (
abst_constr n1 n2))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_and _ _ (fun zenon_He zenon_Hc=>(
zenon_imply _ _ (fun zenon_H10=>(zenon_notand _ _ (fun zenon_Hf=>(
zenon_Hf zenon_He)) (fun zenon_Hd=>(zenon_Hd zenon_Hc)) zenon_H10)) (
fun zenon_Hb=>(zenon_and _ _ (fun zenon_H8 zenon_H6=>(zenon_imply _ _ (
fun zenon_Ha=>(zenon_notand _ _ (fun zenon_H9=>(zenon_H9 zenon_H8)) (
fun zenon_H7=>(zenon_H7 zenon_H6)) zenon_Ha)) (fun zenon_H5=>(zenon_G
zenon_H5)) __E_1_3_LEMMA)) zenon_Hb)) __E_1_2_LEMMA)) __E_1_1_LEMMA)))).
Qed.

      Theorem __E_1_LEMMA :
        Is_true ((abst_equal (abst_constr n3 n4) (abst_constr n1 n2))).
      assert (__force_use_H1 := H1).
      apply for_zenon___E_1_LEMMA;
      auto.
      Qed.
      End __E_1.
(* File "pair.fcl", line 267, characters 2-15 *)
Theorem for_zenon_equal_symmetric2:(forall n1:_p_S1_T,(forall n3
:_p_S1_T,(forall n2:_p_S2_T,(forall n4:_p_S2_T,((Is_true (abst_equal (
abst_constr n1 n2) (abst_constr n3 n4)))->(Is_true (abst_equal (
abst_constr n3 n4) (abst_constr n1 n2)))))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G __E_1_LEMMA)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_symmetric2 :
      forall n1  n3 : _p_S1_T,
        forall n2  n4 : _p_S2_T,
          Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))) ->
            Is_true ((abst_equal (abst_constr n3 n4) (abst_constr n1 n2))).
    assert (__force_use_p_S1_T := _p_S1_T).
    assert (__force_use_p_S2_T := _p_S2_T).
    assert (__force_use__p_S1_equal := _p_S1_equal).
    assert (__force_use__p_S1_equal_symmetric := _p_S1_equal_symmetric).
    assert (__force_use__p_S2_equal := _p_S2_equal).
    assert (__force_use__p_S2_equal_symmetric := _p_S2_equal_symmetric).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_constr := abst_constr).
    assert (__force_use_abst_equal := abst_equal).
    assert (__force_use_abst_def_equal1 := abst_def_equal1).
    apply for_zenon_equal_symmetric2;
    auto.
    Qed.
    End Proof_of_equal_symmetric2.
  
  Theorem equal_symmetric2  (_p_S1_T : Set) (_p_S2_T : Set) (_p_S1_equal :
    _p_S1_T -> _p_S1_T -> basics.bool__t) (_p_S1_equal_symmetric :
    forall x  y : _p_S1_T,
      Is_true ((_p_S1_equal x y)) -> Is_true ((_p_S1_equal y x)))
    (_p_S2_equal : _p_S2_T -> _p_S2_T -> basics.bool__t)
    (_p_S2_equal_symmetric :
    forall x  y : _p_S2_T,
      Is_true ((_p_S2_equal x y)) -> Is_true ((_p_S2_equal y x)))
    (abst_T : Set) (abst_constr : _p_S1_T -> _p_S2_T -> abst_T)
    (abst_equal : abst_T -> abst_T -> basics.bool__t) (abst_def_equal1 :
    forall n1  n3 : _p_S1_T,
      forall n2  n4 : _p_S2_T,
        Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))) <->
          (Is_true ((_p_S1_equal n1 n3)) /\ Is_true ((_p_S2_equal n2 n4)))):
    forall n1  n3 : _p_S1_T,
      forall n2  n4 : _p_S2_T,
        Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))) ->
          Is_true ((abst_equal (abst_constr n3 n4) (abst_constr n1 n2))).
  apply for_zenon_abstracted_equal_symmetric2;
  auto.
  Qed.
  
  (* From species pair#Imp_pair. *)
  (* Section for proof of theorem 'equal_transitive2'. *)
  Section Proof_of_equal_transitive2.
    Variable _p_S1_T : Set.
    Variable _p_S2_T : Set.
    Variable _p_S1_equal : _p_S1_T -> _p_S1_T -> basics.bool__t.
    Variable _p_S1_equal_transitive :
      forall x  y  z : _p_S1_T,
        Is_true ((_p_S1_equal x y)) ->
          Is_true ((_p_S1_equal y z)) -> Is_true ((_p_S1_equal x z)).
    Variable _p_S2_equal : _p_S2_T -> _p_S2_T -> basics.bool__t.
    Variable _p_S2_equal_transitive :
      forall x  y  z : _p_S2_T,
        Is_true ((_p_S2_equal x y)) ->
          Is_true ((_p_S2_equal y z)) -> Is_true ((_p_S2_equal x z)).
    Variable abst_T : Set.
    Variable abst_constr : _p_S1_T -> _p_S2_T -> abst_T.
    Variable abst_equal : abst_T -> abst_T -> basics.bool__t.
    Hypothesis abst_def_equal1 :
      forall n1  n3 : _p_S1_T,
        forall n2  n4 : _p_S2_T,
          Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))) <->
            (Is_true ((_p_S1_equal n1 n3)) /\ Is_true ((_p_S2_equal n2 n4))).
    Section __F_1.
      Variable n1 : _p_S1_T.
      Variable n3 : _p_S1_T.
      Variable n5 : _p_S1_T.
      Variable n2 : _p_S2_T.
      Variable n4 : _p_S2_T.
      Variable n6 : _p_S2_T.
      Variable H1 :
        Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))).
      Variable H2 :
        Is_true ((abst_equal (abst_constr n3 n4) (abst_constr n5 n6))).
      Section __F_1_1.
(* File "pair.fcl", line 300, characters 6-28 *)
Theorem for_zenon___F_1_1_LEMMA:(((Is_true (_p_S1_equal n1 n5))/\(
Is_true (_p_S2_equal n2 n6)))->(Is_true (abst_equal (abst_constr n1 n2)
(abst_constr n5 n6)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notimply _ _ (fun zenon_H9 zenon_H3=>(
zenon_and _ _ (fun zenon_H6 zenon_H4=>(zenon_all _p_S1_T (fun n1
:_p_S1_T=>(forall n3:_p_S1_T,(forall n2:_p_S2_T,(forall n4:_p_S2_T,((
Is_true (abst_equal (abst_constr n1 n2) (abst_constr n3 n4)))<->((
Is_true (_p_S1_equal n1 n3))/\(Is_true (_p_S2_equal n2 n4)))))))) n1 (
fun zenon_Hd=>(zenon_all _p_S1_T (fun n3:_p_S1_T=>(forall n2:_p_S2_T,(
forall n4:_p_S2_T,((Is_true (abst_equal (abst_constr n1 n2) (
abst_constr n3 n4)))<->((Is_true (_p_S1_equal n1 n3))/\(Is_true (
_p_S2_equal n2 n4))))))) n5 (fun zenon_Hc=>(zenon_all _p_S2_T (fun n2
:_p_S2_T=>(forall n4:_p_S2_T,((Is_true (abst_equal (abst_constr n1 n2) (
abst_constr n5 n4)))<->((Is_true (_p_S1_equal n1 n5))/\(Is_true (
_p_S2_equal n2 n4)))))) n2 (fun zenon_Hb=>(zenon_all _p_S2_T (fun n4
:_p_S2_T=>((Is_true (abst_equal (abst_constr n1 n2) (abst_constr n5 n4))
)<->((Is_true (_p_S1_equal n1 n5))/\(Is_true (_p_S2_equal n2 n4))))) n6
(fun zenon_Ha=>(zenon_equiv _ _ (fun zenon_H3 zenon_H8=>(zenon_notand _
_ (fun zenon_H7=>(zenon_H7 zenon_H6)) (fun zenon_H5=>(zenon_H5 zenon_H4)
) zenon_H8)) (fun zenon_H2 zenon_H9=>(zenon_H3 zenon_H2)) zenon_Ha))
zenon_Hb)) zenon_Hc)) zenon_Hd)) abst_def_equal1)) zenon_H9)) zenon_G)))
).
Qed.

        Theorem __F_1_1_LEMMA :
          (Is_true ((_p_S1_equal n1 n5)) /\ Is_true ((_p_S2_equal n2 n6))) ->
            Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n5 n6))).
        assert (__force_use_H1 := H1).
        assert (__force_use_H2 := H2).
        apply for_zenon___F_1_1_LEMMA;
        auto.
        Qed.
        End __F_1_1.
      Section __F_1_2.
(* File "pair.fcl", line 302, characters 6-42 *)
Theorem for_zenon___F_1_2_LEMMA:((Is_true (_p_S1_equal n1 n3))/\(
Is_true (_p_S2_equal n2 n4))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_S1_T (fun n1:_p_S1_T=>(forall n3
:_p_S1_T,(forall n2:_p_S2_T,(forall n4:_p_S2_T,((Is_true (abst_equal (
abst_constr n1 n2) (abst_constr n3 n4)))<->((Is_true (_p_S1_equal n1 n3)
)/\(Is_true (_p_S2_equal n2 n4)))))))) n1 (fun zenon_H8=>(zenon_all
_p_S1_T (fun n3:_p_S1_T=>(forall n2:_p_S2_T,(forall n4:_p_S2_T,((
Is_true (abst_equal (abst_constr n1 n2) (abst_constr n3 n4)))<->((
Is_true (_p_S1_equal n1 n3))/\(Is_true (_p_S2_equal n2 n4))))))) n3 (
fun zenon_H7=>(zenon_all _p_S2_T (fun n2:_p_S2_T=>(forall n4:_p_S2_T,((
Is_true (abst_equal (abst_constr n1 n2) (abst_constr n3 n4)))<->((
Is_true (_p_S1_equal n1 n3))/\(Is_true (_p_S2_equal n2 n4)))))) n2 (fun
zenon_H6=>(zenon_all _p_S2_T (fun n4:_p_S2_T=>((Is_true (abst_equal (
abst_constr n1 n2) (abst_constr n3 n4)))<->((Is_true (_p_S1_equal n1 n3)
)/\(Is_true (_p_S2_equal n2 n4))))) n4 (fun zenon_H5=>(zenon_equiv _ _ (
fun zenon_H4 zenon_G=>(zenon_H4 H1)) (fun H1 zenon_H3=>(zenon_G
zenon_H3)) zenon_H5)) zenon_H6)) zenon_H7)) zenon_H8)) abst_def_equal1))
)).
Qed.

        Theorem __F_1_2_LEMMA :
          (Is_true ((_p_S1_equal n1 n3)) /\ Is_true ((_p_S2_equal n2 n4))).
        assert (__force_use_H1 := H1).
        assert (__force_use_H2 := H2).
        apply for_zenon___F_1_2_LEMMA;
        auto.
        Qed.
        End __F_1_2.
      Section __F_1_3.
(* File "pair.fcl", line 304, characters 6-42 *)
Theorem for_zenon___F_1_3_LEMMA:((Is_true (_p_S1_equal n3 n5))/\(
Is_true (_p_S2_equal n4 n6))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_S1_T (fun n1:_p_S1_T=>(forall n3
:_p_S1_T,(forall n2:_p_S2_T,(forall n4:_p_S2_T,((Is_true (abst_equal (
abst_constr n1 n2) (abst_constr n3 n4)))<->((Is_true (_p_S1_equal n1 n3)
)/\(Is_true (_p_S2_equal n2 n4)))))))) n3 (fun zenon_H8=>(zenon_all
_p_S1_T (fun zenon_Vh:_p_S1_T=>(forall n2:_p_S2_T,(forall n4:_p_S2_T,((
Is_true (abst_equal (abst_constr n3 n2) (abst_constr zenon_Vh n4)))<->((
Is_true (_p_S1_equal n3 zenon_Vh))/\(Is_true (_p_S2_equal n2 n4)))))))
n5 (fun zenon_H7=>(zenon_all _p_S2_T (fun n2:_p_S2_T=>(forall n4
:_p_S2_T,((Is_true (abst_equal (abst_constr n3 n2) (abst_constr n5 n4)))
<->((Is_true (_p_S1_equal n3 n5))/\(Is_true (_p_S2_equal n2 n4)))))) n4
(fun zenon_H6=>(zenon_all _p_S2_T (fun zenon_Vj:_p_S2_T=>((Is_true (
abst_equal (abst_constr n3 n4) (abst_constr n5 zenon_Vj)))<->((Is_true (
_p_S1_equal n3 n5))/\(Is_true (_p_S2_equal n4 zenon_Vj))))) n6 (fun
zenon_H5=>(zenon_equiv _ _ (fun zenon_H4 zenon_G=>(zenon_H4 H2)) (fun
H2 zenon_H3=>(zenon_G zenon_H3)) zenon_H5)) zenon_H6)) zenon_H7))
zenon_H8)) abst_def_equal1)))).
Qed.

        Theorem __F_1_3_LEMMA :
          (Is_true ((_p_S1_equal n3 n5)) /\ Is_true ((_p_S2_equal n4 n6))).
        assert (__force_use_H1 := H1).
        assert (__force_use_H2 := H2).
        apply for_zenon___F_1_3_LEMMA;
        auto.
        Qed.
        End __F_1_3.
(* File "pair.fcl", line 305, character 15, line 306, character 62 *)
Theorem for_zenon___F_1_LEMMA:(Is_true (abst_equal (abst_constr n1 n2) (
abst_constr n5 n6))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_and _ _ (fun zenon_H24 zenon_He=>(
zenon_and _ _ (fun zenon_H1f zenon_H9=>(zenon_imply _ _ (fun zenon_H33=>
(zenon_notand _ _ (fun zenon_H1e=>(let zenon_H30:=(fun zenon_H32=>(
zenon_and _ _ (fun zenon_H2e zenon_H25=>(zenon_H25 zenon_H24))
zenon_H32)) in (let zenon_H1d:=(fun zenon_H31=>(zenon_subst _ (fun
zenon_Vi=>(Is_true zenon_Vi)) (_p_S1_equal n3 n5) (_p_S1_equal n1 n5) (
fun zenon_H20=>(zenon_subst _ (fun zenon_Vj=>(~((_p_S1_equal zenon_Vj
n5) = (_p_S1_equal n1 n5)))) n3 n1 (fun zenon_H2b=>(zenon_notand _ _ (
fun zenon_H2f=>(zenon_H2f (fun zenon_H2d=>(let zenon_H2a:=(fun
zenon_H2c=>(zenon_subst _ (fun zenon_Vk=>(zenon_Vk = n1)) n1 n3 (fun
zenon_H2e=>(zenon_H2e zenon_H2d)) zenon_H2b zenon_H2c)) in (zenon_noteq
_ n1 zenon_H2a))))) (fun zenon_H29=>(zenon_H29 (fun zenon_H24=>(
zenon_all _p_S1_T (fun x:_p_S1_T=>(forall y:_p_S1_T,(forall z:_p_S1_T,((
Is_true (_p_S1_equal x y))->((Is_true (_p_S1_equal y z))->(Is_true (
_p_S1_equal x z))))))) n1 (fun zenon_H28=>(zenon_all _p_S1_T (fun y
:_p_S1_T=>(forall z:_p_S1_T,((Is_true (_p_S1_equal n1 y))->((Is_true (
_p_S1_equal y z))->(Is_true (_p_S1_equal n1 z)))))) n3 (fun zenon_H27=>(
zenon_all _p_S1_T (fun z:_p_S1_T=>((Is_true (_p_S1_equal n1 n3))->((
Is_true (_p_S1_equal n3 z))->(Is_true (_p_S1_equal n1 z))))) n5 (fun
zenon_H26=>(zenon_imply _ _ (fun zenon_H25=>(zenon_H25 zenon_H24)) (fun
zenon_H23=>(zenon_imply _ _ (fun zenon_H22=>(zenon_H22 zenon_H1f)) (fun
zenon_H21=>(zenon_H1e zenon_H21)) zenon_H23)) zenon_H26)) zenon_H27))
zenon_H28)) _p_S1_equal_transitive)))) zenon_H30)) (zenon_notnot _ (
refl_equal (_p_S1_equal n1 n5))) zenon_H20)) zenon_H1e zenon_H1f)) in (
zenon_noteq _ n5 zenon_H1d)))) (fun zenon_H8=>(let zenon_H1a:=(fun
zenon_H1c=>(zenon_and _ _ (fun zenon_H18 zenon_Hf=>(zenon_Hf zenon_He))
zenon_H1c)) in (let zenon_H7:=(fun zenon_H1b=>(zenon_subst _ (fun
zenon_Vf=>(Is_true zenon_Vf)) (_p_S2_equal n4 n6) (_p_S2_equal n2 n6) (
fun zenon_Ha=>(zenon_subst _ (fun zenon_Vg=>(~((_p_S2_equal zenon_Vg n6)
 = (_p_S2_equal n2 n6)))) n4 n2 (fun zenon_H15=>(zenon_notand _ _ (fun
zenon_H19=>(zenon_H19 (fun zenon_H17=>(let zenon_H14:=(fun zenon_H16=>(
zenon_subst _ (fun zenon_Vh=>(zenon_Vh = n2)) n2 n4 (fun zenon_H18=>(
zenon_H18 zenon_H17)) zenon_H15 zenon_H16)) in (zenon_noteq _ n2
zenon_H14))))) (fun zenon_H13=>(zenon_H13 (fun zenon_He=>(zenon_all
_p_S2_T (fun x:_p_S2_T=>(forall y:_p_S2_T,(forall z:_p_S2_T,((Is_true (
_p_S2_equal x y))->((Is_true (_p_S2_equal y z))->(Is_true (_p_S2_equal
x z))))))) n2 (fun zenon_H12=>(zenon_all _p_S2_T (fun y:_p_S2_T=>(
forall z:_p_S2_T,((Is_true (_p_S2_equal n2 y))->((Is_true (_p_S2_equal
y z))->(Is_true (_p_S2_equal n2 z)))))) n4 (fun zenon_H11=>(zenon_all
_p_S2_T (fun z:_p_S2_T=>((Is_true (_p_S2_equal n2 n4))->((Is_true (
_p_S2_equal n4 z))->(Is_true (_p_S2_equal n2 z))))) n6 (fun zenon_H10=>(
zenon_imply _ _ (fun zenon_Hf=>(zenon_Hf zenon_He)) (fun zenon_Hd=>(
zenon_imply _ _ (fun zenon_Hc=>(zenon_Hc zenon_H9)) (fun zenon_Hb=>(
zenon_H8 zenon_Hb)) zenon_Hd)) zenon_H10)) zenon_H11)) zenon_H12))
_p_S2_equal_transitive)))) zenon_H1a)) (zenon_notnot _ (refl_equal (
_p_S2_equal n2 n6))) zenon_Ha)) zenon_H8 zenon_H9)) in (zenon_noteq _
n6 zenon_H7)))) zenon_H33)) (fun zenon_H6=>(zenon_G zenon_H6))
__F_1_1_LEMMA)) __F_1_3_LEMMA)) __F_1_2_LEMMA)))).
Qed.

      Theorem __F_1_LEMMA :
        Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n5 n6))).
      assert (__force_use_H1 := H1).
      assert (__force_use_H2 := H2).
      apply for_zenon___F_1_LEMMA;
      auto.
      Qed.
      End __F_1.
(* File "pair.fcl", line 307, characters 2-15 *)
Theorem for_zenon_equal_transitive2:(forall n1:_p_S1_T,(forall n3
:_p_S1_T,(forall n5:_p_S1_T,(forall n2:_p_S2_T,(forall n4:_p_S2_T,(
forall n6:_p_S2_T,((Is_true (abst_equal (abst_constr n1 n2) (
abst_constr n3 n4)))->((Is_true (abst_equal (abst_constr n3 n4) (
abst_constr n5 n6)))->(Is_true (abst_equal (abst_constr n1 n2) (
abst_constr n5 n6))))))))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G __F_1_LEMMA)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_transitive2 :
      forall n1  n3  n5 : _p_S1_T,
        forall n2  n4  n6 : _p_S2_T,
          Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))) ->
            Is_true ((abst_equal (abst_constr n3 n4) (abst_constr n5 n6))) ->
              Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n5 n6))).
    assert (__force_use_p_S1_T := _p_S1_T).
    assert (__force_use_p_S2_T := _p_S2_T).
    assert (__force_use__p_S1_equal := _p_S1_equal).
    assert (__force_use__p_S1_equal_transitive := _p_S1_equal_transitive).
    assert (__force_use__p_S2_equal := _p_S2_equal).
    assert (__force_use__p_S2_equal_transitive := _p_S2_equal_transitive).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_constr := abst_constr).
    assert (__force_use_abst_equal := abst_equal).
    assert (__force_use_abst_def_equal1 := abst_def_equal1).
    apply for_zenon_equal_transitive2;
    auto.
    Qed.
    End Proof_of_equal_transitive2.
  
  Theorem equal_transitive2  (_p_S1_T : Set) (_p_S2_T : Set) (_p_S1_equal :
    _p_S1_T -> _p_S1_T -> basics.bool__t) (_p_S1_equal_transitive :
    forall x  y  z : _p_S1_T,
      Is_true ((_p_S1_equal x y)) ->
        Is_true ((_p_S1_equal y z)) -> Is_true ((_p_S1_equal x z)))
    (_p_S2_equal : _p_S2_T -> _p_S2_T -> basics.bool__t)
    (_p_S2_equal_transitive :
    forall x  y  z : _p_S2_T,
      Is_true ((_p_S2_equal x y)) ->
        Is_true ((_p_S2_equal y z)) -> Is_true ((_p_S2_equal x z)))
    (abst_T : Set) (abst_constr : _p_S1_T -> _p_S2_T -> abst_T)
    (abst_equal : abst_T -> abst_T -> basics.bool__t) (abst_def_equal1 :
    forall n1  n3 : _p_S1_T,
      forall n2  n4 : _p_S2_T,
        Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))) <->
          (Is_true ((_p_S1_equal n1 n3)) /\ Is_true ((_p_S2_equal n2 n4)))):
    forall n1  n3  n5 : _p_S1_T,
      forall n2  n4  n6 : _p_S2_T,
        Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))) ->
          Is_true ((abst_equal (abst_constr n3 n4) (abst_constr n5 n6))) ->
            Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n5 n6))).
  apply for_zenon_abstracted_equal_transitive2;
  auto.
  Qed.
  
  (* From species pair#Imp_pair. *)
  (* Section for proof of theorem 'equal_symmetric'. *)
  Section Proof_of_equal_symmetric.
    Variable _p_S1_T : Set.
    Variable _p_S2_T : Set.
    Variable abst_T : Set.
    Variable abst_constr : _p_S1_T -> _p_S2_T -> abst_T.
    Variable abst_equal : abst_T -> abst_T -> basics.bool__t.
    Variable abst_prj_a : abst_T -> _p_S1_T.
    Variable abst_prj_b : abst_T -> _p_S2_T.
    Hypothesis abst_unicite_1 :
      forall a : abst_T,
        Is_true ((abst_equal (abst_constr (abst_prj_a a) (abst_prj_b a)) a)).
    Hypothesis abst_unicite_2 :
      forall a : abst_T,
        Is_true ((abst_equal a (abst_constr (abst_prj_a a) (abst_prj_b a)))).
    Hypothesis abst_equal_transitive :
      forall x  y  z : abst_T,
        Is_true ((abst_equal x y)) ->
          Is_true ((abst_equal y z)) -> Is_true ((abst_equal x z)).
    Hypothesis abst_equal_symmetric2 :
      forall n1  n3 : _p_S1_T,
        forall n2  n4 : _p_S2_T,
          Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))) ->
            Is_true ((abst_equal (abst_constr n3 n4) (abst_constr n1 n2))).
    Section __G_1.
      Variable p1 : abst_T.
      Variable p2 : abst_T.
      Variable H1 : Is_true ((abst_equal p1 p2)).
      Section __G_1_1.
(* File "pair.fcl", line 229, characters 9-62 *)
Theorem for_zenon___G_1_1_LEMMA:(Is_true (abst_equal (abst_constr (
abst_prj_a p1) (abst_prj_b p1)) p2)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(let zenon_H15:=(fun zenon_H17=>(zenon_and _ _ (
fun zenon_H13 zenon_Ha=>(zenon_all abst_T (fun a:abst_T=>(Is_true (
abst_equal (abst_constr (abst_prj_a a) (abst_prj_b a)) a))) p1 (fun
zenon_H9=>(zenon_Ha zenon_H9)) abst_unicite_1)) zenon_H17)) in (let
zenon_H4:=(fun zenon_H16=>(zenon_subst _ (fun zenon_Vf=>(Is_true
zenon_Vf)) (abst_equal p1 p2) (abst_equal (abst_constr (abst_prj_a p1) (
abst_prj_b p1)) p2) (fun zenon_H5=>(zenon_subst _ (fun zenon_Vg=>(~((
abst_equal zenon_Vg p2) = (abst_equal (abst_constr (abst_prj_a p1) (
abst_prj_b p1)) p2)))) p1 (abst_constr (abst_prj_a p1) (abst_prj_b p1))
(fun zenon_H10=>(zenon_notand _ _ (fun zenon_H14=>(zenon_H14 (fun
zenon_H12=>(let zenon_Hf:=(fun zenon_H11=>(zenon_subst _ (fun zenon_Vh=>
(zenon_Vh = (abst_constr (abst_prj_a p1) (abst_prj_b p1)))) (
abst_constr (abst_prj_a p1) (abst_prj_b p1)) p1 (fun zenon_H13=>(
zenon_H13 zenon_H12)) zenon_H10 zenon_H11)) in (zenon_noteq _ (
abst_constr (abst_prj_a p1) (abst_prj_b p1)) zenon_Hf))))) (fun
zenon_He=>(zenon_He (fun zenon_H9=>(zenon_all abst_T (fun x:abst_T=>(
forall y:abst_T,(forall z:abst_T,((Is_true (abst_equal x y))->((Is_true
(abst_equal y z))->(Is_true (abst_equal x z))))))) (abst_constr (
abst_prj_a p1) (abst_prj_b p1)) (fun zenon_Hd=>(zenon_all abst_T (fun y
:abst_T=>(forall z:abst_T,((Is_true (abst_equal (abst_constr (
abst_prj_a p1) (abst_prj_b p1)) y))->((Is_true (abst_equal y z))->(
Is_true (abst_equal (abst_constr (abst_prj_a p1) (abst_prj_b p1)) z)))))
) p1 (fun zenon_Hc=>(zenon_all abst_T (fun z:abst_T=>((Is_true (
abst_equal (abst_constr (abst_prj_a p1) (abst_prj_b p1)) p1))->((
Is_true (abst_equal p1 z))->(Is_true (abst_equal (abst_constr (
abst_prj_a p1) (abst_prj_b p1)) z))))) p2 (fun zenon_Hb=>(zenon_imply _
_ (fun zenon_Ha=>(zenon_Ha zenon_H9)) (fun zenon_H8=>(zenon_imply _ _ (
fun zenon_H7=>(zenon_H7 H1)) (fun zenon_H6=>(zenon_G zenon_H6))
zenon_H8)) zenon_Hb)) zenon_Hc)) zenon_Hd)) abst_equal_transitive))))
zenon_H15)) (zenon_notnot _ (refl_equal (abst_equal (abst_constr (
abst_prj_a p1) (abst_prj_b p1)) p2))) zenon_H5)) zenon_G H1)) in (
zenon_noteq _ p2 zenon_H4)))))).
Qed.

        Theorem __G_1_1_LEMMA :
          Is_true ((abst_equal (abst_constr (abst_prj_a p1) (abst_prj_b p1))
                     p2)).
        assert (__force_use_H1 := H1).
        apply for_zenon___G_1_1_LEMMA;
        auto.
        Qed.
        End __G_1_1.
      Section __G_1_2.
(* File "pair.fcl", line 232, characters 9-58 *)
Theorem for_zenon___G_1_2_LEMMA:(Is_true (abst_equal (abst_constr (
abst_prj_a p1) (abst_prj_b p1)) (abst_constr (abst_prj_a p2) (
abst_prj_b p2)))).
Proof.
exact(
let zenon_L1_:((~(Is_true (abst_equal p2 (abst_constr (abst_prj_a p2) (
abst_prj_b p2)))))->False):=
(fun zenon_H4:(~(Is_true (abst_equal p2 (abst_constr (abst_prj_a p2) (
abst_prj_b p2)))))=>(zenon_all abst_T (fun a:abst_T=>(Is_true (
abst_equal a (abst_constr (abst_prj_a a) (abst_prj_b a))))) p2 (fun
zenon_H5=>(zenon_H4 zenon_H5)) abst_unicite_2))in
(NNPP _ (fun zenon_G=>(let zenon_H4:=(fun zenon_H5=>(zenon_all abst_T (
fun x:abst_T=>(forall y:abst_T,(forall z:abst_T,((Is_true (abst_equal x
y))->((Is_true (abst_equal y z))->(Is_true (abst_equal x z))))))) (
abst_constr (abst_prj_a p1) (abst_prj_b p1)) (fun zenon_Hb=>(zenon_all
abst_T (fun y:abst_T=>(forall z:abst_T,((Is_true (abst_equal (
abst_constr (abst_prj_a p1) (abst_prj_b p1)) y))->((Is_true (abst_equal
y z))->(Is_true (abst_equal (abst_constr (abst_prj_a p1) (abst_prj_b p1)
) z)))))) p2 (fun zenon_Ha=>(zenon_all abst_T (fun z:abst_T=>((Is_true (
abst_equal (abst_constr (abst_prj_a p1) (abst_prj_b p1)) p2))->((
Is_true (abst_equal p2 z))->(Is_true (abst_equal (abst_constr (
abst_prj_a p1) (abst_prj_b p1)) z))))) (abst_constr (abst_prj_a p2) (
abst_prj_b p2)) (fun zenon_H9=>(zenon_imply _ _ (fun zenon_H8=>(
zenon_H8 __G_1_1_LEMMA)) (fun zenon_H7=>(zenon_imply _ _ (fun zenon_H4=>
(zenon_H4 zenon_H5)) (fun zenon_H6=>(zenon_G zenon_H6)) zenon_H7))
zenon_H9)) zenon_Ha)) zenon_Hb)) abst_equal_transitive)) in (zenon_L1_
zenon_H4))))).
Qed.

        Theorem __G_1_2_LEMMA :
          Is_true ((abst_equal (abst_constr (abst_prj_a p1) (abst_prj_b p1))
                     (abst_constr (abst_prj_a p2) (abst_prj_b p2)))).
        assert (__force_use_H1 := H1).
        apply for_zenon___G_1_2_LEMMA;
        auto.
        Qed.
        End __G_1_2.
      Section __G_1_3.
(* File "pair.fcl", line 235, characters 9-47 *)
Theorem for_zenon___G_1_3_LEMMA:(Is_true (abst_equal (abst_constr (
abst_prj_a p2) (abst_prj_b p2)) (abst_constr (abst_prj_a p1) (
abst_prj_b p1)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_all _p_S1_T (fun n1:_p_S1_T=>(forall n3
:_p_S1_T,(forall n2:_p_S2_T,(forall n4:_p_S2_T,((Is_true (abst_equal (
abst_constr n1 n2) (abst_constr n3 n4)))->(Is_true (abst_equal (
abst_constr n3 n4) (abst_constr n1 n2)))))))) (abst_prj_a p1) (fun
zenon_H8=>(zenon_all _p_S1_T (fun n3:_p_S1_T=>(forall n2:_p_S2_T,(
forall n4:_p_S2_T,((Is_true (abst_equal (abst_constr (abst_prj_a p1) n2)
 (abst_constr n3 n4)))->(Is_true (abst_equal (abst_constr n3 n4) (
abst_constr (abst_prj_a p1) n2))))))) (abst_prj_a p2) (fun zenon_H7=>(
zenon_all _p_S2_T (fun n2:_p_S2_T=>(forall n4:_p_S2_T,((Is_true (
abst_equal (abst_constr (abst_prj_a p1) n2) (abst_constr (abst_prj_a p2)
 n4)))->(Is_true (abst_equal (abst_constr (abst_prj_a p2) n4) (
abst_constr (abst_prj_a p1) n2)))))) (abst_prj_b p1) (fun zenon_H6=>(
zenon_all _p_S2_T (fun n4:_p_S2_T=>((Is_true (abst_equal (abst_constr (
abst_prj_a p1) (abst_prj_b p1)) (abst_constr (abst_prj_a p2) n4)))->(
Is_true (abst_equal (abst_constr (abst_prj_a p2) n4) (abst_constr (
abst_prj_a p1) (abst_prj_b p1)))))) (abst_prj_b p2) (fun zenon_H5=>(
zenon_imply _ _ (fun zenon_H4=>(zenon_H4 __G_1_2_LEMMA)) (fun zenon_H3=>
(zenon_G zenon_H3)) zenon_H5)) zenon_H6)) zenon_H7)) zenon_H8))
abst_equal_symmetric2)))).
Qed.

        Theorem __G_1_3_LEMMA :
          Is_true ((abst_equal (abst_constr (abst_prj_a p2) (abst_prj_b p2))
                     (abst_constr (abst_prj_a p1) (abst_prj_b p1)))).
        assert (__force_use_H1 := H1).
        apply for_zenon___G_1_3_LEMMA;
        auto.
        Qed.
        End __G_1_3.
      Section __G_1_4.
(* File "pair.fcl", line 238, characters 9-58 *)
Theorem for_zenon___G_1_4_LEMMA:(Is_true (abst_equal p2 (abst_constr (
abst_prj_a p1) (abst_prj_b p1)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(let zenon_H15:=(fun zenon_H17=>(zenon_and _ _ (
fun zenon_H13 zenon_Ha=>(zenon_all abst_T (fun a:abst_T=>(Is_true (
abst_equal a (abst_constr (abst_prj_a a) (abst_prj_b a))))) p2 (fun
zenon_H9=>(zenon_Ha zenon_H9)) abst_unicite_2)) zenon_H17)) in (let
zenon_H4:=(fun zenon_H16=>(zenon_subst _ (fun zenon_Vf=>(Is_true
zenon_Vf)) (abst_equal (abst_constr (abst_prj_a p2) (abst_prj_b p2)) (
abst_constr (abst_prj_a p1) (abst_prj_b p1))) (abst_equal p2 (
abst_constr (abst_prj_a p1) (abst_prj_b p1))) (fun zenon_H5=>(
zenon_subst _ (fun zenon_Vg=>(~((abst_equal zenon_Vg (abst_constr (
abst_prj_a p1) (abst_prj_b p1))) = (abst_equal p2 (abst_constr (
abst_prj_a p1) (abst_prj_b p1)))))) (abst_constr (abst_prj_a p2) (
abst_prj_b p2)) p2 (fun zenon_H10=>(zenon_notand _ _ (fun zenon_H14=>(
zenon_H14 (fun zenon_H12=>(let zenon_Hf:=(fun zenon_H11=>(zenon_subst _
(fun zenon_Vh=>(zenon_Vh = p2)) p2 (abst_constr (abst_prj_a p2) (
abst_prj_b p2)) (fun zenon_H13=>(zenon_H13 zenon_H12)) zenon_H10
zenon_H11)) in (zenon_noteq _ p2 zenon_Hf))))) (fun zenon_He=>(zenon_He
(fun zenon_H9=>(zenon_all abst_T (fun x:abst_T=>(forall y:abst_T,(
forall z:abst_T,((Is_true (abst_equal x y))->((Is_true (abst_equal y z))
->(Is_true (abst_equal x z))))))) p2 (fun zenon_Hd=>(zenon_all abst_T (
fun y:abst_T=>(forall z:abst_T,((Is_true (abst_equal p2 y))->((Is_true (
abst_equal y z))->(Is_true (abst_equal p2 z)))))) (abst_constr (
abst_prj_a p2) (abst_prj_b p2)) (fun zenon_Hc=>(zenon_all abst_T (fun z
:abst_T=>((Is_true (abst_equal p2 (abst_constr (abst_prj_a p2) (
abst_prj_b p2))))->((Is_true (abst_equal (abst_constr (abst_prj_a p2) (
abst_prj_b p2)) z))->(Is_true (abst_equal p2 z))))) (abst_constr (
abst_prj_a p1) (abst_prj_b p1)) (fun zenon_Hb=>(zenon_imply _ _ (fun
zenon_Ha=>(zenon_Ha zenon_H9)) (fun zenon_H8=>(zenon_imply _ _ (fun
zenon_H7=>(zenon_H7 __G_1_3_LEMMA)) (fun zenon_H6=>(zenon_G zenon_H6))
zenon_H8)) zenon_Hb)) zenon_Hc)) zenon_Hd)) abst_equal_transitive))))
zenon_H15)) (zenon_notnot _ (refl_equal (abst_equal p2 (abst_constr (
abst_prj_a p1) (abst_prj_b p1))))) zenon_H5)) zenon_G __G_1_3_LEMMA))
in (zenon_noteq _ (abst_constr (abst_prj_a p1) (abst_prj_b p1))
zenon_H4)))))).
Qed.

        Theorem __G_1_4_LEMMA :
          Is_true ((abst_equal p2
                     (abst_constr (abst_prj_a p1) (abst_prj_b p1)))).
        assert (__force_use_H1 := H1).
        apply for_zenon___G_1_4_LEMMA;
        auto.
        Qed.
        End __G_1_4.
(* File "pair.fcl", line 240, characters 13-62 *)
Theorem for_zenon___G_1_LEMMA:(Is_true (abst_equal p2 p1)).
Proof.
exact(
(NNPP _ (fun zenon_G=>(let zenon_H5:=(fun zenon_H4=>(zenon_all abst_T (
fun x:abst_T=>(forall y:abst_T,(forall z:abst_T,((Is_true (abst_equal x
y))->((Is_true (abst_equal y z))->(Is_true (abst_equal x z))))))) p2 (
fun zenon_Hb=>(zenon_all abst_T (fun y:abst_T=>(forall z:abst_T,((
Is_true (abst_equal p2 y))->((Is_true (abst_equal y z))->(Is_true (
abst_equal p2 z)))))) (abst_constr (abst_prj_a p1) (abst_prj_b p1)) (
fun zenon_Ha=>(zenon_all abst_T (fun z:abst_T=>((Is_true (abst_equal p2
(abst_constr (abst_prj_a p1) (abst_prj_b p1))))->((Is_true (abst_equal (
abst_constr (abst_prj_a p1) (abst_prj_b p1)) z))->(Is_true (abst_equal
p2 z))))) p1 (fun zenon_H9=>(zenon_imply _ _ (fun zenon_H8=>(zenon_H8
__G_1_4_LEMMA)) (fun zenon_H7=>(zenon_imply _ _ (fun zenon_H5=>(
zenon_H5 zenon_H4)) (fun zenon_H6=>(zenon_G zenon_H6)) zenon_H7))
zenon_H9)) zenon_Ha)) zenon_Hb)) abst_equal_transitive)) in (zenon_all
abst_T (fun a:abst_T=>(Is_true (abst_equal (abst_constr (abst_prj_a a) (
abst_prj_b a)) a))) p1 (fun zenon_H4=>(zenon_H5 zenon_H4))
abst_unicite_1))))).
Qed.

      Theorem __G_1_LEMMA : Is_true ((abst_equal p2 p1)).
      assert (__force_use_H1 := H1).
      apply for_zenon___G_1_LEMMA;
      auto.
      Qed.
      End __G_1.
(* File "pair.fcl", line 242, characters 2-15 *)
Theorem for_zenon_equal_symmetric:(forall p1:abst_T,(forall p2:abst_T,((
Is_true (abst_equal p1 p2))->(Is_true (abst_equal p2 p1))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_G __G_1_LEMMA)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_equal_symmetric :
      forall x  y : abst_T,
        Is_true ((abst_equal x y)) -> Is_true ((abst_equal y x)).
    assert (__force_use_p_S1_T := _p_S1_T).
    assert (__force_use_p_S2_T := _p_S2_T).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_constr := abst_constr).
    assert (__force_use_abst_equal := abst_equal).
    assert (__force_use_abst_prj_a := abst_prj_a).
    assert (__force_use_abst_prj_b := abst_prj_b).
    assert (__force_use_abst_unicite_1 := abst_unicite_1).
    assert (__force_use_abst_unicite_2 := abst_unicite_2).
    assert (__force_use_abst_equal_transitive := abst_equal_transitive).
    assert (__force_use_abst_equal_symmetric2 := abst_equal_symmetric2).
    apply for_zenon_equal_symmetric;
    auto.
    Qed.
    End Proof_of_equal_symmetric.
  
  Theorem equal_symmetric  (_p_S1_T : Set) (_p_S2_T : Set) (abst_T : Set)
    (abst_constr : _p_S1_T -> _p_S2_T -> abst_T)
    (abst_equal : abst_T -> abst_T -> basics.bool__t)
    (abst_prj_a : abst_T -> _p_S1_T) (abst_prj_b : abst_T -> _p_S2_T)
    (abst_unicite_1 :
    forall a : abst_T,
      Is_true ((abst_equal (abst_constr (abst_prj_a a) (abst_prj_b a)) a)))
    (abst_unicite_2 :
    forall a : abst_T,
      Is_true ((abst_equal a (abst_constr (abst_prj_a a) (abst_prj_b a)))))
    (abst_equal_transitive :
    forall x  y  z : abst_T,
      Is_true ((abst_equal x y)) ->
        Is_true ((abst_equal y z)) -> Is_true ((abst_equal x z)))
    (abst_equal_symmetric2 :
    forall n1  n3 : _p_S1_T,
      forall n2  n4 : _p_S2_T,
        Is_true ((abst_equal (abst_constr n1 n2) (abst_constr n3 n4))) ->
          Is_true ((abst_equal (abst_constr n3 n4) (abst_constr n1 n2)))):
    forall x  y : abst_T,
      Is_true ((abst_equal x y)) -> Is_true ((abst_equal y x)).
  apply for_zenon_abstracted_equal_symmetric;
  auto.
  Qed.
  
  (* Fully defined 'Imp_pair' species's collection generator. *)
  Definition collection_create (_p_S1_T : Set) (_p_S2_T : Set) _p_S1_element
    _p_S1_equal _p_S1_equal_reflexive _p_S1_equal_symmetric
    _p_S1_equal_transitive _p_S2_element _p_S2_equal _p_S2_equal_reflexive
    _p_S2_equal_symmetric _p_S2_equal_transitive :=
    let local_rep := (Datatypes.prod _p_S1_T _p_S2_T) in
    (* From species pair#Imp_pair. *)
    let local_constr := constr _p_S1_T _p_S2_T in
    (* From species pair#Imp_pair. *)
    let local_equal := equal _p_S1_T _p_S2_T _p_S1_equal _p_S2_equal in
    (* From species basics#Basic_object. *)
    let local_parse := basics.Basic_object.parse local_rep in
    (* From species basics#Basic_object. *)
    let local_print := basics.Basic_object.print local_rep in
    (* From species pair#Imp_pair. *)
    let local_prj_a := prj_a _p_S1_T _p_S2_T in
    (* From species pair#Imp_pair. *)
    let local_prj_b := prj_b _p_S1_T _p_S2_T in
    (* From species pair#Imp_pair. *)
    let local_element := element _p_S1_T _p_S2_T _p_S1_element _p_S2_element
      local_rep local_constr in
    (* From species sets#Setoid. *)
    let local_different := sets.Setoid.different local_rep local_equal in
    (* From species pair#Imp_pair. *)
    let local_prj_a_is_first_of_pair := prj_a_is_first_of_pair _p_S1_T
      _p_S2_T _p_S1_equal local_rep local_constr local_prj_a in
    (* From species pair#Imp_pair. *)
    let local_def_equal := def_equal _p_S1_T _p_S2_T _p_S1_equal _p_S2_equal
      local_rep local_equal local_prj_a local_prj_b in
    (* From species pair#Imp_pair. *)
    let local_prj_b_is_snd_of_pair := prj_b_is_snd_of_pair _p_S1_T _p_S2_T
      _p_S2_equal local_rep local_constr local_prj_b in
    (* From species pair#Imp_pair. *)
    let local_unicite_1 := unicite_1 _p_S1_T _p_S2_T local_rep local_constr
      local_equal local_prj_a local_prj_b in
    (* From species pair#Imp_pair. *)
    let local_unicite_2 := unicite_2 _p_S1_T _p_S2_T local_rep local_constr
      local_equal local_prj_a local_prj_b in
    (* From species sets#Setoid. *)
    let local_same_is_not_different := sets.Setoid.same_is_not_different
      local_rep local_equal in
    (* From species pair#Imp_pair. *)
    let local_equal_transitive := equal_transitive _p_S1_T _p_S2_T
      _p_S1_equal _p_S1_equal_transitive _p_S2_equal _p_S2_equal_transitive
      local_rep local_equal local_prj_a local_prj_b local_def_equal in
    (* From species pair#Imp_pair. *)
    let local_def_equal1 := def_equal1 _p_S1_T _p_S2_T _p_S1_equal
      _p_S1_equal_symmetric _p_S1_equal_transitive _p_S2_equal
      _p_S2_equal_symmetric _p_S2_equal_transitive local_rep local_constr
      local_equal local_prj_a local_prj_b local_prj_a_is_first_of_pair
      local_def_equal local_prj_b_is_snd_of_pair in
    (* From species pair#Imp_pair. *)
    let local_equal_reflexive := equal_reflexive _p_S1_T _p_S2_T local_rep
      local_constr local_equal local_prj_a local_prj_b local_unicite_1
      local_unicite_2 local_equal_transitive in
    (* From species pair#Imp_pair. *)
    let local_equal_reflexive2 := equal_reflexive2 _p_S1_T _p_S2_T
      _p_S1_equal _p_S1_equal_reflexive _p_S2_equal _p_S2_equal_reflexive
      local_rep local_constr local_equal local_def_equal1 in
    (* From species pair#Imp_pair. *)
    let local_equal_symmetric2 := equal_symmetric2 _p_S1_T _p_S2_T
      _p_S1_equal _p_S1_equal_symmetric _p_S2_equal _p_S2_equal_symmetric
      local_rep local_constr local_equal local_def_equal1 in
    (* From species pair#Imp_pair. *)
    let local_equal_transitive2 := equal_transitive2 _p_S1_T _p_S2_T
      _p_S1_equal _p_S1_equal_transitive _p_S2_equal _p_S2_equal_transitive
      local_rep local_constr local_equal local_def_equal1 in
    (* From species sets#Setoid. *)
    let local_different_is_irreflexive :=
      sets.Setoid.different_is_irreflexive local_rep local_equal
      local_different local_equal_reflexive local_same_is_not_different in
    (* From species pair#Imp_pair. *)
    let local_equal_symmetric := equal_symmetric _p_S1_T _p_S2_T local_rep
      local_constr local_equal local_prj_a local_prj_b local_unicite_1
      local_unicite_2 local_equal_transitive local_equal_symmetric2 in
    (* From species sets#Setoid. *)
    let local_different_is_complete := sets.Setoid.different_is_complete
      local_rep local_equal local_different local_equal_reflexive
      local_equal_symmetric local_equal_transitive
      local_same_is_not_different in
    (* From species sets#Setoid. *)
    let local_different_is_symmetric := sets.Setoid.different_is_symmetric
      local_rep local_equal local_different local_equal_symmetric
      local_same_is_not_different in
    mk_record (_p_S1_T : Set) (_p_S2_T : Set) _p_S1_equal _p_S2_equal
    local_rep local_constr local_equal local_parse local_print local_prj_a
    local_prj_b local_element local_different local_prj_a_is_first_of_pair
    local_def_equal local_prj_b_is_snd_of_pair local_unicite_1
    local_unicite_2 local_same_is_not_different local_equal_transitive
    local_def_equal1 local_equal_reflexive local_equal_reflexive2
    local_equal_symmetric2 local_equal_transitive2
    local_different_is_irreflexive local_equal_symmetric
    local_different_is_complete local_different_is_symmetric.
  
End Imp_pair.

