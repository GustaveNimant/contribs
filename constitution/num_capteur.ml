module Sp_capteur =
  struct
  end ;;

module Imp_capteur =
  struct
  type ('p0_T, 'abst_T) me_as_species = {
    (* From species num_capteur#Imp_capteur. *)
    rf_capt_1 : 'abst_T ;
    (* From species num_capteur#Imp_capteur. *)
    rf_equal : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species basics#Basic_object. *)
    rf_parse : Basics._focty_string -> 'abst_T ;
    (* From species num_capteur#Imp_capteur. *)
    rf_capt_2 : 'abst_T ;
    (* From species num_capteur#Imp_capteur. *)
    rf_element : 'abst_T ;
    (* From species sets#Setoid. *)
    rf_different : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species num_capteur#Imp_capteur. *)
    rf_capt_3 : 'abst_T ;
    (* From species num_capteur#Imp_capteur. *)
    rf_print : 'abst_T -> Basics._focty_string ;
    }
  let capt_1 _p_P_zero = _p_P_zero
  let equal _p_P_equal (x : 'abst_T) (y : 'abst_T) = (_p_P_equal x y)
  let capt_2 _p_P_s abst_capt_1 = (_p_P_s abst_capt_1)
  let element abst_capt_1 = abst_capt_1
  let capt_3 _p_P_s abst_capt_2 = (_p_P_s abst_capt_2)
  let print abst_capt_1 abst_equal abst_capt_2 abst_capt_3 (x : 'abst_T) =
    if (abst_equal x abst_capt_1) then "capt_1"
      else if (abst_equal x abst_capt_2) then "capt_2"
             else if (abst_equal x abst_capt_3) then "capt_3"
                    else "Erreur capteur"
  (* Fully defined 'Imp_capteur' species's collection generator. *)
  let collection_create () _p_P_equal _p_P_s _p_P_zero =
    (* From species num_capteur#Imp_capteur. *)
    let local_capt_1 = capt_1 _p_P_zero in
    (* From species num_capteur#Imp_capteur. *)
    let local_equal = equal _p_P_equal in
    (* From species basics#Basic_object. *)
    let local_parse = Basics.Basic_object.parse in
    (* From species num_capteur#Imp_capteur. *)
    let local_capt_2 = capt_2 _p_P_s local_capt_1 in
    (* From species num_capteur#Imp_capteur. *)
    let local_element = element local_capt_1 in
    (* From species sets#Setoid. *)
    let local_different = Sets.Setoid.different local_equal in
    (* From species num_capteur#Imp_capteur. *)
    let local_capt_3 = capt_3 _p_P_s local_capt_2 in
    (* From species num_capteur#Imp_capteur. *)
    let local_print = print local_capt_1 local_equal local_capt_2
      local_capt_3 in
    { rf_capt_1 = local_capt_1 ;
      rf_equal = local_equal ;
      rf_parse = local_parse ;
      rf_capt_2 = local_capt_2 ;
      rf_element = local_element ;
      rf_different = local_different ;
      rf_capt_3 = local_capt_3 ;
      rf_print = local_print ;
       }
    
  end ;;

module type Coll_capteurSig = sig
  type me_as_carrier
  (* From species num_capteur#Imp_capteur. *)
  val capt_1 : me_as_carrier
  (* From species num_capteur#Imp_capteur. *)
  val equal : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species basics#Basic_object. *)
  val parse : Basics._focty_string -> me_as_carrier
  (* From species num_capteur#Imp_capteur. *)
  val capt_2 : me_as_carrier
  (* From species num_capteur#Imp_capteur. *)
  val element : me_as_carrier
  (* From species sets#Setoid. *)
  val different : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species num_capteur#Imp_capteur. *)
  val capt_3 : me_as_carrier
  (* From species num_capteur#Imp_capteur. *)
  val print : me_as_carrier -> Basics._focty_string
  end

module Coll_capteur : Coll_capteurSig =
  struct
  (* Carrier's structure explicitly given by "rep". *)
  type me_as_carrier = Peano.Coll_peano.me_as_carrier
  let effective_collection =
    Imp_capteur.collection_create () Peano.Coll_peano.equal
    Peano.Coll_peano.s Peano.Coll_peano.zero
  let capt_1 = effective_collection.Imp_capteur.rf_capt_1
  let equal = effective_collection.Imp_capteur.rf_equal
  let parse = effective_collection.Imp_capteur.rf_parse
  let capt_2 = effective_collection.Imp_capteur.rf_capt_2
  let element = effective_collection.Imp_capteur.rf_element
  let different = effective_collection.Imp_capteur.rf_different
  let capt_3 = effective_collection.Imp_capteur.rf_capt_3
  let print = effective_collection.Imp_capteur.rf_print
  end ;;

