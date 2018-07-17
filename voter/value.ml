module Sp_value_tol =
  struct
  end ;;

module Imp_value_tol =
  struct
  let consistency_rule _p_T_geq _p_T_plus _p_tol_tol (x : 'abst_T)
    (y : 'abst_T) =
    if (_p_T_geq x y) then (_p_T_geq (_p_T_plus y _p_tol_tol) x)
      else (_p_T_geq (_p_T_plus x _p_tol_tol) y)
  let element _p_T_element = _p_T_element
  let equal _p_T_equal (x : 'abst_T) (y : 'abst_T) = (_p_T_equal x y)
  let parse _p_T_parse (x : Basics._focty_string) = (_p_T_parse x)
  let print _p_T_print (x : 'abst_T) = (_p_T_print x)
  end ;;

module Sp_value =
  struct
  end ;;

module Imp_value =
  struct
  type ('t0_T, 'abst_T) me_as_species = {
    (* From species value#Imp_value. *)
    rf_consistency_rule : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species value#Imp_value. *)
    rf_element : 'abst_T ;
    (* From species value#Imp_value. *)
    rf_equal : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species value#Imp_value. *)
    rf_parse : Basics._focty_string -> 'abst_T ;
    (* From species value#Imp_value. *)
    rf_print : 'abst_T -> Basics._focty_string ;
    (* From species sets#Setoid. *)
    rf_different : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    }
  let consistency_rule _p_T_equal (x : 'abst_T) (y : 'abst_T) =
    (_p_T_equal x y)
  let element _p_T_element = _p_T_element
  let equal _p_T_equal (x : 'abst_T) (y : 'abst_T) = (_p_T_equal x y)
  let parse _p_T_parse (x : Basics._focty_string) = (_p_T_parse x)
  let print _p_T_print (x : 'abst_T) = (_p_T_print x)
  (* Fully defined 'Imp_value' species's collection generator. *)
  let collection_create () _p_T_element _p_T_equal _p_T_parse _p_T_print =
    (* From species value#Imp_value. *)
    let local_consistency_rule = consistency_rule _p_T_equal in
    (* From species value#Imp_value. *)
    let local_element = element _p_T_element in
    (* From species value#Imp_value. *)
    let local_equal = equal _p_T_equal in
    (* From species value#Imp_value. *)
    let local_parse = parse _p_T_parse in
    (* From species value#Imp_value. *)
    let local_print = print _p_T_print in
    (* From species sets#Setoid. *)
    let local_different = Sets.Setoid.different local_equal in
    { rf_consistency_rule = local_consistency_rule ;
      rf_element = local_element ;
      rf_equal = local_equal ;
      rf_parse = local_parse ;
      rf_print = local_print ;
      rf_different = local_different ;
       }
    
  end ;;

module Spe_int_imp_value_tol2 =
  struct
  type 'abst_T me_as_species = {
    (* From species value#Imp_value_tol. *)
    rf_consistency_rule : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species value#Imp_value_tol. *)
    rf_element : 'abst_T ;
    (* From species value#Imp_value_tol. *)
    rf_equal : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species value#Imp_value_tol. *)
    rf_parse : Basics._focty_string -> 'abst_T ;
    (* From species value#Imp_value_tol. *)
    rf_print : 'abst_T -> Basics._focty_string ;
    (* From species sets#Setoid. *)
    rf_different : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    }
  (* Fully defined 'Spe_int_imp_value_tol2' species's collection generator. *)
  let collection_create () =
    (* From species value#Imp_value_tol. *)
    let local_consistency_rule = Imp_value_tol.consistency_rule
      Basic_type.Coll_int_value.geq Basic_type.Coll_int_value.plus
      ((Basic_type.Coll_int_value.of_int 2)) in
    (* From species value#Imp_value_tol. *)
    let local_element = Imp_value_tol.element
      Basic_type.Coll_int_value.element in
    (* From species value#Imp_value_tol. *)
    let local_equal = Imp_value_tol.equal Basic_type.Coll_int_value.equal in
    (* From species value#Imp_value_tol. *)
    let local_parse = Imp_value_tol.parse Basic_type.Coll_int_value.parse in
    (* From species value#Imp_value_tol. *)
    let local_print = Imp_value_tol.print Basic_type.Coll_int_value.print in
    (* From species sets#Setoid. *)
    let local_different = Sets.Setoid.different local_equal in
    { rf_consistency_rule = local_consistency_rule ;
      rf_element = local_element ;
      rf_equal = local_equal ;
      rf_parse = local_parse ;
      rf_print = local_print ;
      rf_different = local_different ;
       }
    
  end ;;

module type Coll_int_imp_value_tolSig = sig
  type me_as_carrier
  (* From species value#Imp_value_tol. *)
  val consistency_rule : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species value#Imp_value_tol. *)
  val element : me_as_carrier
  (* From species value#Imp_value_tol. *)
  val equal : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species value#Imp_value_tol. *)
  val parse : Basics._focty_string -> me_as_carrier
  (* From species value#Imp_value_tol. *)
  val print : me_as_carrier -> Basics._focty_string
  (* From species sets#Setoid. *)
  val different : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  end

module Coll_int_imp_value_tol : Coll_int_imp_value_tolSig =
  struct
  (* Carrier's structure explicitly given by "rep". *)
  type me_as_carrier = Basic_type.Coll_int_value.me_as_carrier
  let effective_collection =
    Spe_int_imp_value_tol2.collection_create ()
  let consistency_rule =
    effective_collection.Spe_int_imp_value_tol2.rf_consistency_rule
  let element = effective_collection.Spe_int_imp_value_tol2.rf_element
  let equal = effective_collection.Spe_int_imp_value_tol2.rf_equal
  let parse = effective_collection.Spe_int_imp_value_tol2.rf_parse
  let print = effective_collection.Spe_int_imp_value_tol2.rf_print
  let different = effective_collection.Spe_int_imp_value_tol2.rf_different
  end ;;

module type Coll_int_imp_valueSig = sig
  type me_as_carrier
  (* From species value#Imp_value. *)
  val consistency_rule : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species value#Imp_value. *)
  val element : me_as_carrier
  (* From species value#Imp_value. *)
  val equal : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species value#Imp_value. *)
  val parse : Basics._focty_string -> me_as_carrier
  (* From species value#Imp_value. *)
  val print : me_as_carrier -> Basics._focty_string
  (* From species sets#Setoid. *)
  val different : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  end

module Coll_int_imp_value : Coll_int_imp_valueSig =
  struct
  (* Carrier's structure explicitly given by "rep". *)
  type me_as_carrier = Basic_type.Coll_int_value.me_as_carrier
  let effective_collection =
    Imp_value.collection_create () Basic_type.Coll_int_value.element
    Basic_type.Coll_int_value.equal Basic_type.Coll_int_value.parse
    Basic_type.Coll_int_value.print
  let consistency_rule = effective_collection.Imp_value.rf_consistency_rule
  let element = effective_collection.Imp_value.rf_element
  let equal = effective_collection.Imp_value.rf_equal
  let parse = effective_collection.Imp_value.rf_parse
  let print = effective_collection.Imp_value.rf_print
  let different = effective_collection.Imp_value.rf_different
  end ;;

module type Coll_bool_imp_valueSig = sig
  type me_as_carrier
  (* From species value#Imp_value. *)
  val consistency_rule : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species value#Imp_value. *)
  val element : me_as_carrier
  (* From species value#Imp_value. *)
  val equal : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species value#Imp_value. *)
  val parse : Basics._focty_string -> me_as_carrier
  (* From species value#Imp_value. *)
  val print : me_as_carrier -> Basics._focty_string
  (* From species sets#Setoid. *)
  val different : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  end

module Coll_bool_imp_value : Coll_bool_imp_valueSig =
  struct
  (* Carrier's structure explicitly given by "rep". *)
  type me_as_carrier = Basic_type.Coll_bool_value.me_as_carrier
  let effective_collection =
    Imp_value.collection_create () Basic_type.Coll_bool_value.element
    Basic_type.Coll_bool_value.equal Basic_type.Coll_bool_value.parse
    Basic_type.Coll_bool_value.print
  let consistency_rule = effective_collection.Imp_value.rf_consistency_rule
  let element = effective_collection.Imp_value.rf_element
  let equal = effective_collection.Imp_value.rf_equal
  let parse = effective_collection.Imp_value.rf_parse
  let print = effective_collection.Imp_value.rf_print
  let different = effective_collection.Imp_value.rf_different
  end ;;

