module Sp_valid_meas =
  struct
  end ;;

module Imp_valid_meas =
  struct
  type ('p0_T, 'abst_T) me_as_species = {
    (* From species valid_meas#Imp_valid_meas. *)
    rf_equal : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species valid_meas#Imp_valid_meas. *)
    rf_valid : 'abst_T ;
    (* From species sets#Setoid. *)
    rf_different : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species valid_meas#Imp_valid_meas. *)
    rf_invalid : 'abst_T ;
    (* From species valid_meas#Imp_valid_meas. *)
    rf_element : 'abst_T ;
    (* From species valid_meas#Imp_valid_meas. *)
    rf_parse : Basics._focty_string -> 'abst_T ;
    (* From species valid_meas#Imp_valid_meas. *)
    rf_print : 'abst_T -> Basics._focty_string ;
    }
  let equal _p_P_equal (x : 'abst_T) (y : 'abst_T) = (_p_P_equal x y)
  let valid _p_P_zero = _p_P_zero
  let invalid _p_P_s abst_valid = (_p_P_s abst_valid)
  let element abst_invalid = abst_invalid
  let parse abst_valid abst_invalid (x : Basics._focty_string) =
    if (Basics._equal_ x "valid") then abst_valid
      else if (Basics._equal_ x "invalid") then abst_invalid
             else (Basics.focalize_error "Erreur parse valid_meas")
  let print abst_equal abst_valid abst_invalid (x : 'abst_T) =
    if (abst_equal x abst_valid) then "valid measure"
      else if (abst_equal x abst_invalid) then "invalid measure"
             else "Erreur capteur"
  (* Fully defined 'Imp_valid_meas' species's collection generator. *)
  let collection_create () _p_P_equal _p_P_s _p_P_zero =
    (* From species valid_meas#Imp_valid_meas. *)
    let local_equal = equal _p_P_equal in
    (* From species valid_meas#Imp_valid_meas. *)
    let local_valid = valid _p_P_zero in
    (* From species sets#Setoid. *)
    let local_different = Sets.Setoid.different local_equal in
    (* From species valid_meas#Imp_valid_meas. *)
    let local_invalid = invalid _p_P_s local_valid in
    (* From species valid_meas#Imp_valid_meas. *)
    let local_element = element local_invalid in
    (* From species valid_meas#Imp_valid_meas. *)
    let local_parse = parse local_valid local_invalid in
    (* From species valid_meas#Imp_valid_meas. *)
    let local_print = print local_equal local_valid local_invalid in
    { rf_equal = local_equal ;
      rf_valid = local_valid ;
      rf_different = local_different ;
      rf_invalid = local_invalid ;
      rf_element = local_element ;
      rf_parse = local_parse ;
      rf_print = local_print ;
       }
    
  end ;;

module type Coll_valid_measSig = sig
  type me_as_carrier
  (* From species valid_meas#Imp_valid_meas. *)
  val equal : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species valid_meas#Imp_valid_meas. *)
  val valid : me_as_carrier
  (* From species sets#Setoid. *)
  val different : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species valid_meas#Imp_valid_meas. *)
  val invalid : me_as_carrier
  (* From species valid_meas#Imp_valid_meas. *)
  val element : me_as_carrier
  (* From species valid_meas#Imp_valid_meas. *)
  val parse : Basics._focty_string -> me_as_carrier
  (* From species valid_meas#Imp_valid_meas. *)
  val print : me_as_carrier -> Basics._focty_string
  end

module Coll_valid_meas : Coll_valid_measSig =
  struct
  (* Carrier's structure explicitly given by "rep". *)
  type me_as_carrier = Peano.Coll_peano.me_as_carrier
  let effective_collection =
    Imp_valid_meas.collection_create () Peano.Coll_peano.equal
    Peano.Coll_peano.s Peano.Coll_peano.zero
  let equal = effective_collection.Imp_valid_meas.rf_equal
  let valid = effective_collection.Imp_valid_meas.rf_valid
  let different = effective_collection.Imp_valid_meas.rf_different
  let invalid = effective_collection.Imp_valid_meas.rf_invalid
  let element = effective_collection.Imp_valid_meas.rf_element
  let parse = effective_collection.Imp_valid_meas.rf_parse
  let print = effective_collection.Imp_valid_meas.rf_print
  end ;;

