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
Require basics.
Module Peano.
  Definition induction (abst_T : Set) (abst_s : abst_T -> abst_T)
    (abst_zero : abst_T) (p : abst_T -> basics.bool__t) :
    coq_builtins.prop__t :=
    Is_true ((p abst_zero)) ->
      (forall n : abst_T, Is_true ((p n)) -> Is_true ((p (abst_s n)))) ->
        (forall n : abst_T, Is_true ((p n))).
  
End Peano.

Module Imp_peano.
  Record me_as_species : Type :=
    mk_record {
    rf_T : Set ;
    (* From species peano#Imp_peano. *)
    rf_diff : rf_T -> rf_T -> basics.bool__t ;
    (* From species peano#Imp_peano. *)
    rf_equal : rf_T -> rf_T -> basics.bool__t ;
    (* From species peano#Imp_peano. *)
    rf_s : rf_T -> rf_T ;
    (* From species peano#Imp_peano. *)
    rf_zero : rf_T ;
    (* From species peano#Imp_peano. *)
    rf_diff_spec :
      forall x  y : rf_T,
        Is_true ((rf_diff x y)) <-> ~Is_true ((rf_equal x y)) ;
    (* From species peano#Imp_peano. *)
    rf_equal_reflexive : forall x : rf_T, Is_true ((rf_equal x x)) ;
    (* From species peano#Imp_peano. *)
    rf_equal_symmetric :
      forall x  y : rf_T,
        Is_true ((rf_equal x y)) -> Is_true ((rf_equal y x)) ;
    (* From species peano#Imp_peano. *)
    rf_equal_transitive :
      forall x  y  z : rf_T,
        (Is_true ((rf_equal x y)) /\ Is_true ((rf_equal y z))) ->
          Is_true ((rf_equal x z)) ;
    (* From species peano#Imp_peano. *)
    rf_succ_is_an_injection :
      forall x  y : rf_T,
        Is_true ((rf_equal (rf_s x) (rf_s y))) -> Is_true ((rf_equal x y)) ;
    (* From species peano#Peano. *)
    rf_induction : (rf_T -> basics.bool__t) -> coq_builtins.prop__t ;
    (* From species peano#Imp_peano. *)
    rf_zero_is_not_successor :
      forall x : rf_T, ~Is_true ((rf_equal rf_zero (rf_s x))) ;
    (* From species peano#Imp_peano. *)
    rf_diff_is_irreflexive : forall x : rf_T, ~Is_true ((rf_diff x x)) ;
    (* From species peano#Imp_peano. *)
    rf_diff_is_symmetric :
      forall x  y : rf_T,
        (~Is_true ((rf_diff x y))) -> (~Is_true ((rf_diff y x)))
    }.
  
  Definition diff (abst_T : Set) (x : abst_T) (y : abst_T) :
    basics.bool__t := (if (((basics._equal_ _) x y)) then false else true).
  Definition equal (abst_T : Set) (x : abst_T) (y : abst_T) :
    basics.bool__t := (((basics._equal_ _) x y)).
  Definition s (abst_T := basics.int__t) (x : abst_T) : abst_T :=
    (basics.int_succ x).
  Definition zero (abst_T := basics.int__t) : abst_T := 0.
  
  (* From species peano#Imp_peano. *)
  (* Section for proof of theorem 'diff_spec'. *)
  Section Proof_of_diff_spec.
    Variable abst_T : Set.
    Let abst_diff := diff abst_T.
    Let abst_equal := equal
    abst_T.
(* File "peano.fcl", line 133, characters 2-30 *)
Theorem for_zenon_diff_spec:(forall x:abst_T,(forall y:abst_T,((Is_true
(abst_diff x y))<->(~(Is_true (abst_equal x y)))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>(forall y:abst_T,((
Is_true (abst_diff x y))<->(~(Is_true (abst_equal x y)))))) (fun
zenon_H13=>(zenon_ex abst_T (fun x:abst_T=>(~(forall y:abst_T,((Is_true
(abst_diff x y))<->(~(Is_true (abst_equal x y))))))) (fun(zenon_Tx_b
:abst_T) zenon_H12=>(zenon_notallex (fun y:abst_T=>((Is_true (abst_diff
zenon_Tx_b y))<->(~(Is_true (abst_equal zenon_Tx_b y))))) (fun
zenon_H11=>(zenon_ex abst_T (fun y:abst_T=>(~((Is_true (abst_diff
zenon_Tx_b y))<->(~(Is_true (abst_equal zenon_Tx_b y)))))) (fun(
zenon_Ty_c:abst_T) zenon_H10=>(zenon_notequiv _ _ (fun zenon_Hf
zenon_He=>(let zenon_Hd:=zenon_Hf in (let zenon_H5:=zenon_He in (
zenon_focal_ite_bool_n (basics._equal_ _ zenon_Tx_b zenon_Ty_c) false
true (fun zenon_H4 zenon_Hc=>(zenon_H5 zenon_H4)) (fun zenon_H5
zenon_Hb=>(zenon_focal_nottrue zenon_Hb)) zenon_Hd)))) (fun zenon_H8
zenon_Ha=>(zenon_Ha (fun zenon_H9=>(let zenon_H4:=zenon_H9 in (let
zenon_H7:=zenon_H8 in (zenon_focal_ite_bool (basics._equal_ _
zenon_Tx_b zenon_Ty_c) false true (fun zenon_H4 zenon_H3=>(
zenon_focal_false zenon_H3)) (fun zenon_H5 zenon_H6=>(zenon_H5 zenon_H4)
) zenon_H7)))))) zenon_H10)) zenon_H11)) zenon_H12)) zenon_H13))
zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_diff_spec :
      forall x  y : abst_T,
        Is_true ((abst_diff x y)) <-> ~Is_true ((abst_equal x y)).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_diff := abst_diff).
    assert (__force_use_abst_equal := abst_equal).
    apply for_zenon_diff_spec;
    auto.
    Qed.
    End Proof_of_diff_spec.
  
  Theorem diff_spec  (abst_T : Set) (abst_diff := diff abst_T) (abst_equal :=
    equal abst_T):
    forall x  y : abst_T,
      Is_true ((abst_diff x y)) <-> ~Is_true ((abst_equal x y)).
  apply for_zenon_abstracted_diff_spec;
  auto.
  Qed.
  
  (* From species peano#Imp_peano. *)
  (* Section for proof of theorem 'equal_reflexive'. *)
  Section Proof_of_equal_reflexive.
    Variable abst_T : Set.
    Let abst_equal := equal
    abst_T.
(* File "peano.fcl", line 116, character 2, line 117, character 19 *)
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
  
  (* From species peano#Imp_peano. *)
  (* Section for proof of theorem 'equal_symmetric'. *)
  Section Proof_of_equal_symmetric.
    Variable abst_T : Set.
    Let abst_equal := equal
    abst_T.
(* File "peano.fcl", line 121, character 2, line 122, character 19 *)
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
  
  (* From species peano#Imp_peano. *)
  (* Section for proof of theorem 'equal_transitive'. *)
  Section Proof_of_equal_transitive.
    Variable abst_T : Set.
    Let abst_equal := equal
    abst_T.
(* File "peano.fcl", line 126, character 2, line 127, character 20 *)
Theorem for_zenon_equal_transitive:(forall x:abst_T,(forall y:abst_T,(
forall z:abst_T,(((Is_true (abst_equal x y))/\(Is_true (abst_equal y z))
)->(Is_true (abst_equal x z)))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>(forall y:abst_T,(
forall z:abst_T,(((Is_true (abst_equal x y))/\(Is_true (abst_equal y z))
)->(Is_true (abst_equal x z)))))) (fun zenon_H15=>(zenon_ex abst_T (fun
x:abst_T=>(~(forall y:abst_T,(forall z:abst_T,(((Is_true (abst_equal x
y))/\(Is_true (abst_equal y z)))->(Is_true (abst_equal x z))))))) (fun(
zenon_Tx_c:abst_T) zenon_H14=>(zenon_notallex (fun y:abst_T=>(forall z
:abst_T,(((Is_true (abst_equal zenon_Tx_c y))/\(Is_true (abst_equal y z)
))->(Is_true (abst_equal zenon_Tx_c z))))) (fun zenon_H13=>(zenon_ex
abst_T (fun y:abst_T=>(~(forall z:abst_T,(((Is_true (abst_equal
zenon_Tx_c y))/\(Is_true (abst_equal y z)))->(Is_true (abst_equal
zenon_Tx_c z)))))) (fun(zenon_Ty_d:abst_T) zenon_H12=>(zenon_notallex (
fun z:abst_T=>(((Is_true (abst_equal zenon_Tx_c zenon_Ty_d))/\(Is_true (
abst_equal zenon_Ty_d z)))->(Is_true (abst_equal zenon_Tx_c z)))) (fun
zenon_H11=>(zenon_ex abst_T (fun z:abst_T=>(~(((Is_true (abst_equal
zenon_Tx_c zenon_Ty_d))/\(Is_true (abst_equal zenon_Ty_d z)))->(Is_true
(abst_equal zenon_Tx_c z))))) (fun(zenon_Tz_e:abst_T) zenon_H10=>(
zenon_notimply _ _ (fun zenon_Hf zenon_Ha=>(zenon_and _ _ (fun zenon_He
zenon_Hc=>(let zenon_Hd:=zenon_He in (
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
        (Is_true ((abst_equal x y)) /\ Is_true ((abst_equal y z))) ->
          Is_true ((abst_equal x z)).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_equal := abst_equal).
    apply for_zenon_equal_transitive;
    auto.
    Qed.
    End Proof_of_equal_transitive.
  
  Theorem equal_transitive  (abst_T : Set) (abst_equal := equal abst_T):
    forall x  y  z : abst_T,
      (Is_true ((abst_equal x y)) /\ Is_true ((abst_equal y z))) ->
        Is_true ((abst_equal x z)).
  apply for_zenon_abstracted_equal_transitive;
  auto.
  Qed.
  
  (* From species peano#Imp_peano. *)
  Theorem succ_is_an_injection  (abst_T : Set)
    (abst_equal : abst_T -> abst_T -> basics.bool__t)
    (abst_s : abst_T -> abst_T):
    forall x  y : abst_T,
      Is_true ((abst_equal (abst_s x) (abst_s y))) ->
        Is_true ((abst_equal x y)).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
  (* From species peano#Imp_peano. *)
  Theorem zero_is_not_successor  (abst_T : Set)
    (abst_equal : abst_T -> abst_T -> basics.bool__t)
    (abst_s : abst_T -> abst_T) (abst_zero : abst_T):
    forall x : abst_T, ~Is_true ((abst_equal abst_zero (abst_s x))).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
  (* From species peano#Imp_peano. *)
  (* Section for proof of theorem 'diff_is_irreflexive'. *)
  Section Proof_of_diff_is_irreflexive.
    Variable abst_T : Set.
    Let abst_diff := diff
    abst_T.
    Variable abst_equal : abst_T -> abst_T -> basics.bool__t.
    Hypothesis abst_equal_reflexive :
      forall x : abst_T, Is_true ((abst_equal x x)).
(* File "peano.fcl", line 137, character 2, line 138, character 26 *)
Theorem for_zenon_diff_is_irreflexive:(forall x:abst_T,(~(Is_true (
abst_diff x x)))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>(~(Is_true (
abst_diff x x)))) (fun zenon_Hb=>(zenon_ex abst_T (fun x:abst_T=>(~(~(
Is_true (abst_diff x x))))) (fun(zenon_Tx_c:abst_T) zenon_Ha=>(zenon_Ha
(fun zenon_H9=>(let zenon_H8:=zenon_H9 in (zenon_focal_ite_bool (
basics._equal_ _ zenon_Tx_c zenon_Tx_c) false true (fun zenon_H6
zenon_H3=>(zenon_focal_false zenon_H3)) (fun zenon_H5 zenon_H7=>(
coq_builtins.zenon_not_syntactic_equal _ zenon_Tx_c zenon_Tx_c (fun
zenon_H4=>(zenon_noteq _ zenon_Tx_c zenon_H4)) zenon_H5)) zenon_H8)))))
zenon_Hb)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_diff_is_irreflexive :
      forall x : abst_T, ~Is_true ((abst_diff x x)).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_diff := abst_diff).
    assert (__force_use_abst_equal := abst_equal).
    assert (__force_use_abst_equal_reflexive := abst_equal_reflexive).
    apply for_zenon_diff_is_irreflexive;
    auto.
    Qed.
    End Proof_of_diff_is_irreflexive.
  
  Theorem diff_is_irreflexive  (abst_T : Set) (abst_diff := diff abst_T)
    (abst_equal : abst_T -> abst_T -> basics.bool__t) (abst_equal_reflexive :
    forall x : abst_T, Is_true ((abst_equal x x))):
    forall x : abst_T, ~Is_true ((abst_diff x x)).
  apply for_zenon_abstracted_diff_is_irreflexive;
  auto.
  Qed.
  
  (* From species peano#Imp_peano. *)
  (* Section for proof of theorem 'diff_is_symmetric'. *)
  Section Proof_of_diff_is_symmetric.
    Variable abst_T : Set.
    Let abst_diff := diff
    abst_T.
    Variable abst_equal : abst_T -> abst_T -> basics.bool__t.
    Hypothesis abst_equal_symmetric :
      forall x  y : abst_T,
        Is_true ((abst_equal x y)) -> Is_true ((abst_equal y x)).
(* File "peano.fcl", line 142, character 2, line 143, character 26 *)
Theorem for_zenon_diff_is_symmetric:(forall x:abst_T,(forall y:abst_T,((
~(Is_true (abst_diff x y)))->(~(Is_true (abst_diff y x)))))).
Proof.
exact(
(NNPP _ (fun zenon_G=>(zenon_notallex (fun x:abst_T=>(forall y:abst_T,((
~(Is_true (abst_diff x y)))->(~(Is_true (abst_diff y x)))))) (fun
zenon_H16=>(zenon_ex abst_T (fun x:abst_T=>(~(forall y:abst_T,((~(
Is_true (abst_diff x y)))->(~(Is_true (abst_diff y x))))))) (fun(
zenon_Tx_c:abst_T) zenon_H15=>(zenon_notallex (fun y:abst_T=>((~(
Is_true (abst_diff zenon_Tx_c y)))->(~(Is_true (abst_diff y zenon_Tx_c))
))) (fun zenon_H14=>(zenon_ex abst_T (fun y:abst_T=>(~((~(Is_true (
abst_diff zenon_Tx_c y)))->(~(Is_true (abst_diff y zenon_Tx_c)))))) (
fun(zenon_Ty_d:abst_T) zenon_H13=>(zenon_notimply _ _ (fun zenon_H10
zenon_H12=>(zenon_H12 (fun zenon_H11=>(let zenon_Hb:=zenon_H11 in (let
zenon_Hf:=zenon_H10 in (zenon_focal_ite_bool_n (basics._equal_ _
zenon_Tx_c zenon_Ty_d) false true (fun zenon_Hc zenon_H5=>(
coq_builtins.zenon_syntactic_equal zenon_focal_eqdec _ zenon_Tx_c
zenon_Ty_d (fun zenon_H6=>(zenon_focal_ite_bool (basics._equal_ _
zenon_Ty_d zenon_Tx_c) false true (fun zenon_H9 zenon_H4=>(zenon_H5
zenon_H4)) (fun zenon_H8 zenon_Ha=>(
coq_builtins.zenon_not_syntactic_equal _ zenon_Ty_d zenon_Tx_c (fun
zenon_H7=>(zenon_eqsym _ zenon_Tx_c zenon_Ty_d zenon_H6 zenon_H7))
zenon_H8)) zenon_Hb)) zenon_Hc)) (fun zenon_He zenon_Hd=>(
zenon_focal_nottrue zenon_Hd)) zenon_Hf)))))) zenon_H13)) zenon_H14))
zenon_H15)) zenon_H16)) zenon_G)))).
Qed.

    (* Dummy theorem to enforce Coq abstractions. *)
    Theorem for_zenon_abstracted_diff_is_symmetric :
      forall x  y : abst_T,
        (~Is_true ((abst_diff x y))) -> (~Is_true ((abst_diff y x))).
    assert (__force_use_abst_T := abst_T).
    assert (__force_use_abst_diff := abst_diff).
    assert (__force_use_abst_equal := abst_equal).
    assert (__force_use_abst_equal_symmetric := abst_equal_symmetric).
    apply for_zenon_diff_is_symmetric;
    auto.
    Qed.
    End Proof_of_diff_is_symmetric.
  
  Theorem diff_is_symmetric  (abst_T : Set) (abst_diff := diff abst_T)
    (abst_equal : abst_T -> abst_T -> basics.bool__t) (abst_equal_symmetric :
    forall x  y : abst_T,
      Is_true ((abst_equal x y)) -> Is_true ((abst_equal y x))):
    forall x  y : abst_T,
      (~Is_true ((abst_diff x y))) -> (~Is_true ((abst_diff y x))).
  apply for_zenon_abstracted_diff_is_symmetric;
  auto.
  Qed.
  
  (* Fully defined 'Imp_peano' species's collection generator. *)
  Definition collection_create :=
    let local_rep := basics.int__t in
    (* From species peano#Imp_peano. *)
    let local_diff := diff local_rep in
    (* From species peano#Imp_peano. *)
    let local_equal := equal local_rep in
    (* From species peano#Imp_peano. *)
    let local_s := s in
    (* From species peano#Imp_peano. *)
    let local_zero := zero in
    (* From species peano#Imp_peano. *)
    let local_diff_spec := diff_spec local_rep in
    (* From species peano#Imp_peano. *)
    let local_equal_reflexive := equal_reflexive local_rep in
    (* From species peano#Imp_peano. *)
    let local_equal_symmetric := equal_symmetric local_rep in
    (* From species peano#Imp_peano. *)
    let local_equal_transitive := equal_transitive local_rep in
    (* From species peano#Imp_peano. *)
    let local_succ_is_an_injection := succ_is_an_injection local_rep
      local_equal local_s in
    (* From species peano#Peano. *)
    let local_induction := Peano.induction local_rep local_s local_zero in
    (* From species peano#Imp_peano. *)
    let local_zero_is_not_successor := zero_is_not_successor local_rep
      local_equal local_s local_zero in
    (* From species peano#Imp_peano. *)
    let local_diff_is_irreflexive := diff_is_irreflexive local_rep
      local_equal local_equal_reflexive in
    (* From species peano#Imp_peano. *)
    let local_diff_is_symmetric := diff_is_symmetric local_rep local_equal
      local_equal_symmetric in
    mk_record local_rep local_diff local_equal local_s local_zero
    local_diff_spec local_equal_reflexive local_equal_symmetric
    local_equal_transitive local_succ_is_an_injection local_induction
    local_zero_is_not_successor local_diff_is_irreflexive
    local_diff_is_symmetric.
  
End Imp_peano.

Module Coll_peano.
  Let effective_collection := Imp_peano.collection_create.
  (* Carrier's structure explicitly given by "rep". *)
  Definition me_as_carrier := basics.int__t.
  Definition diff := effective_collection.(Imp_peano.rf_diff).
  Definition equal := effective_collection.(Imp_peano.rf_equal).
  Definition s := effective_collection.(Imp_peano.rf_s).
  Definition zero := effective_collection.(Imp_peano.rf_zero).
  Definition diff_spec := effective_collection.(Imp_peano.rf_diff_spec).
  Definition equal_reflexive :=
    effective_collection.(Imp_peano.rf_equal_reflexive).
  Definition equal_symmetric :=
    effective_collection.(Imp_peano.rf_equal_symmetric).
  Definition equal_transitive :=
    effective_collection.(Imp_peano.rf_equal_transitive).
  Definition succ_is_an_injection :=
    effective_collection.(Imp_peano.rf_succ_is_an_injection).
  Definition induction := effective_collection.(Imp_peano.rf_induction).
  Definition zero_is_not_successor :=
    effective_collection.(Imp_peano.rf_zero_is_not_successor).
  Definition diff_is_irreflexive :=
    effective_collection.(Imp_peano.rf_diff_is_irreflexive).
  Definition diff_is_symmetric :=
    effective_collection.(Imp_peano.rf_diff_is_symmetric).
  
End Coll_peano.

Module Peano_Arith.
  
  (* From species peano#Peano_Arith. *)
  Theorem plus_commutative  (abst_T : Set)
    (abst_equal : abst_T -> abst_T -> basics.bool__t)
    (abst_plus : abst_T -> abst_T -> abst_T):
    forall x  y : abst_T,
      Is_true ((abst_equal (abst_plus x y) (abst_plus y x))).
  (* Proof was flagged as assumed *)
  apply coq_builtins.magic_prove.
  Qed.
  
End Peano_Arith.

