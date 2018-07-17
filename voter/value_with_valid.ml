module Sp_value_with_valid =
  struct
  end ;;

module Imp_value_with_valid =
  struct
  type ('t0_T, 'v1_T, 'abst_T) me_as_species = {
    (* From species pair#Imp_pair. *)
    rf_constr : 't0_T -> 'v1_T -> 'abst_T ;
    (* From species pair#Imp_pair. *)
    rf_equal : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species basics#Basic_object. *)
    rf_parse : Basics._focty_string -> 'abst_T ;
    (* From species pair#Imp_pair. *)
    rf_prj_a : 'abst_T -> 't0_T ;
    (* From species pair#Imp_pair. *)
    rf_prj_b : 'abst_T -> 'v1_T ;
    (* From species pair#Imp_pair. *)
    rf_element : 'abst_T ;
    (* From species value_with_valid#Imp_value_with_valid. *)
    rf_parse2 : Basics._focty_string -> Basics._focty_string -> 'abst_T ;
    (* From species sets#Setoid. *)
    rf_different : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species value_with_valid#Imp_value_with_valid. *)
    rf_consistency_rule : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species value_with_valid#Imp_value_with_valid. *)
    rf_print : 'abst_T -> Basics._focty_string ;
    }
  let parse2 _p_T_parse _p_V_parse abst_constr (x : Basics._focty_string)
    (y : Basics._focty_string) = (abst_constr (_p_T_parse x) (_p_V_parse y))
  let consistency_rule _p_T_equal _p_V_equal _p_V_valid abst_prj_a abst_prj_b
    (x : 'abst_T) (y : 'abst_T) =
    if (_p_V_equal (abst_prj_b x) _p_V_valid)
      then if (_p_V_equal (abst_prj_b y) _p_V_valid)
             then (_p_T_equal (abst_prj_a x) (abst_prj_a y)) else false
      else if (_p_V_equal (abst_prj_b y) _p_V_valid) then false else true
  let print _p_T_print _p_V_print abst_prj_a abst_prj_b (x : 'abst_T) =
    let a = "( " in
    let b = (_p_T_print (abst_prj_a x)) in
    let c = ", " in
    let d = (_p_V_print (abst_prj_b x)) in
    let e = ")"
    in
    (Basics._hat_ a (Basics._hat_ b (Basics._hat_ c (Basics._hat_ d e))))
  (* Fully defined 'Imp_value_with_valid' species's collection generator. *)
  let collection_create () _p_V_element _p_V_equal _p_V_valid _p_V_parse
    _p_V_print _p_T_element _p_T_equal _p_T_parse _p_T_print =
    (* From species pair#Imp_pair. *)
    let local_constr = Pair.Imp_pair.constr in
    (* From species pair#Imp_pair. *)
    let local_equal = Pair.Imp_pair.equal _p_T_equal _p_V_equal in
    (* From species basics#Basic_object. *)
    let local_parse = Basics.Basic_object.parse in
    (* From species pair#Imp_pair. *)
    let local_prj_a = Pair.Imp_pair.prj_a in
    (* From species pair#Imp_pair. *)
    let local_prj_b = Pair.Imp_pair.prj_b in
    (* From species pair#Imp_pair. *)
    let local_element = Pair.Imp_pair.element _p_T_element _p_V_element
      local_constr in
    (* From species value_with_valid#Imp_value_with_valid. *)
    let local_parse2 = parse2 _p_T_parse _p_V_parse local_constr in
    (* From species sets#Setoid. *)
    let local_different = Sets.Setoid.different local_equal in
    (* From species value_with_valid#Imp_value_with_valid. *)
    let local_consistency_rule = consistency_rule _p_T_equal _p_V_equal
      _p_V_valid local_prj_a local_prj_b in
    (* From species value_with_valid#Imp_value_with_valid. *)
    let local_print = print _p_T_print _p_V_print local_prj_a local_prj_b in
    { rf_constr = local_constr ;
      rf_equal = local_equal ;
      rf_parse = local_parse ;
      rf_prj_a = local_prj_a ;
      rf_prj_b = local_prj_b ;
      rf_element = local_element ;
      rf_parse2 = local_parse2 ;
      rf_different = local_different ;
      rf_consistency_rule = local_consistency_rule ;
      rf_print = local_print ;
       }
    
  end ;;

module type Coll_int_value_with_validSig = sig
  type me_as_carrier
  (* From species pair#Imp_pair. *)
  val constr : Basic_type.Coll_int_value.me_as_carrier ->
                 Valid_meas.Coll_valid_meas.me_as_carrier -> me_as_carrier
  (* From species pair#Imp_pair. *)
  val equal : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species basics#Basic_object. *)
  val parse : Basics._focty_string -> me_as_carrier
  (* From species pair#Imp_pair. *)
  val prj_a : me_as_carrier -> Basic_type.Coll_int_value.me_as_carrier
  (* From species pair#Imp_pair. *)
  val prj_b : me_as_carrier -> Valid_meas.Coll_valid_meas.me_as_carrier
  (* From species pair#Imp_pair. *)
  val element : me_as_carrier
  (* From species value_with_valid#Imp_value_with_valid. *)
  val parse2 : Basics._focty_string -> Basics._focty_string -> me_as_carrier
  (* From species sets#Setoid. *)
  val different : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species value_with_valid#Imp_value_with_valid. *)
  val consistency_rule : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species value_with_valid#Imp_value_with_valid. *)
  val print : me_as_carrier -> Basics._focty_string
  end

module Coll_int_value_with_valid : Coll_int_value_with_validSig =
  struct
  (* Carrier's structure explicitly given by "rep". *)
  type me_as_carrier =
    Basic_type.Coll_int_value.me_as_carrier *
      Valid_meas.Coll_valid_meas.me_as_carrier
  let effective_collection =
    Imp_value_with_valid.collection_create ()
    Valid_meas.Coll_valid_meas.element Valid_meas.Coll_valid_meas.equal
    Valid_meas.Coll_valid_meas.valid Valid_meas.Coll_valid_meas.parse
    Valid_meas.Coll_valid_meas.print Basic_type.Coll_int_value.element
    Basic_type.Coll_int_value.equal Basic_type.Coll_int_value.parse
    Basic_type.Coll_int_value.print
  let constr = effective_collection.Imp_value_with_valid.rf_constr
  let equal = effective_collection.Imp_value_with_valid.rf_equal
  let parse = effective_collection.Imp_value_with_valid.rf_parse
  let prj_a = effective_collection.Imp_value_with_valid.rf_prj_a
  let prj_b = effective_collection.Imp_value_with_valid.rf_prj_b
  let element = effective_collection.Imp_value_with_valid.rf_element
  let parse2 = effective_collection.Imp_value_with_valid.rf_parse2
  let different = effective_collection.Imp_value_with_valid.rf_different
  let consistency_rule =
    effective_collection.Imp_value_with_valid.rf_consistency_rule
  let print = effective_collection.Imp_value_with_valid.rf_print
  end ;;

