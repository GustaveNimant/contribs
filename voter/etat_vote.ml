module Sp_etat_vote =
  struct
  end ;;

module Imp_etat_vote =
  struct
  type ('p0_T, 'abst_T) me_as_species = {
    (* From species etat_vote#Imp_etat_vote. *)
    rf_equal : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species etat_vote#Imp_etat_vote. *)
    rf_no_match : 'abst_T ;
    (* From species basics#Basic_object. *)
    rf_parse : Basics._focty_string -> 'abst_T ;
    (* From species sets#Setoid. *)
    rf_different : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species etat_vote#Imp_etat_vote. *)
    rf_element : 'abst_T ;
    (* From species etat_vote#Imp_etat_vote. *)
    rf_range_match : 'abst_T ;
    (* From species etat_vote#Imp_etat_vote. *)
    rf_partial_match : 'abst_T ;
    (* From species etat_vote#Imp_etat_vote. *)
    rf_perfect_match : 'abst_T ;
    (* From species etat_vote#Imp_etat_vote. *)
    rf_print : 'abst_T -> Basics._focty_string ;
    }
  let equal _p_P_equal (x : 'abst_T) (y : 'abst_T) = (_p_P_equal x y)
  let no_match _p_P_zero = _p_P_zero
  let element abst_no_match = abst_no_match
  let range_match _p_P_s abst_no_match = (_p_P_s abst_no_match)
  let partial_match _p_P_s abst_range_match = (_p_P_s abst_range_match)
  let perfect_match _p_P_s abst_partial_match = (_p_P_s abst_partial_match)
  let print abst_equal abst_no_match abst_range_match abst_partial_match
    abst_perfect_match (x : 'abst_T) =
    if (abst_equal x abst_no_match) then "no_match"
      else if (abst_equal x abst_range_match) then "range_match"
             else if (abst_equal x abst_partial_match) then "partial_match"
                    else if (abst_equal x abst_perfect_match)
                           then "perfect_match" else "Erreur etat_vote"
  (* Fully defined 'Imp_etat_vote' species's collection generator. *)
  let collection_create () _p_P_equal _p_P_s _p_P_zero =
    (* From species etat_vote#Imp_etat_vote. *)
    let local_equal = equal _p_P_equal in
    (* From species etat_vote#Imp_etat_vote. *)
    let local_no_match = no_match _p_P_zero in
    (* From species basics#Basic_object. *)
    let local_parse = Basics.Basic_object.parse in
    (* From species sets#Setoid. *)
    let local_different = Sets.Setoid.different local_equal in
    (* From species etat_vote#Imp_etat_vote. *)
    let local_element = element local_no_match in
    (* From species etat_vote#Imp_etat_vote. *)
    let local_range_match = range_match _p_P_s local_no_match in
    (* From species etat_vote#Imp_etat_vote. *)
    let local_partial_match = partial_match _p_P_s local_range_match in
    (* From species etat_vote#Imp_etat_vote. *)
    let local_perfect_match = perfect_match _p_P_s local_partial_match in
    (* From species etat_vote#Imp_etat_vote. *)
    let local_print = print local_equal local_no_match local_range_match
      local_partial_match local_perfect_match in
    { rf_equal = local_equal ;
      rf_no_match = local_no_match ;
      rf_parse = local_parse ;
      rf_different = local_different ;
      rf_element = local_element ;
      rf_range_match = local_range_match ;
      rf_partial_match = local_partial_match ;
      rf_perfect_match = local_perfect_match ;
      rf_print = local_print ;
       }
    
  end ;;

module type Coll_etat_voteSig = sig
  type me_as_carrier
  (* From species etat_vote#Imp_etat_vote. *)
  val equal : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species etat_vote#Imp_etat_vote. *)
  val no_match : me_as_carrier
  (* From species basics#Basic_object. *)
  val parse : Basics._focty_string -> me_as_carrier
  (* From species sets#Setoid. *)
  val different : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species etat_vote#Imp_etat_vote. *)
  val element : me_as_carrier
  (* From species etat_vote#Imp_etat_vote. *)
  val range_match : me_as_carrier
  (* From species etat_vote#Imp_etat_vote. *)
  val partial_match : me_as_carrier
  (* From species etat_vote#Imp_etat_vote. *)
  val perfect_match : me_as_carrier
  (* From species etat_vote#Imp_etat_vote. *)
  val print : me_as_carrier -> Basics._focty_string
  end

module Coll_etat_vote : Coll_etat_voteSig =
  struct
  (* Carrier's structure explicitly given by "rep". *)
  type me_as_carrier = Peano.Coll_peano.me_as_carrier
  let effective_collection =
    Imp_etat_vote.collection_create () Peano.Coll_peano.equal
    Peano.Coll_peano.s Peano.Coll_peano.zero
  let equal = effective_collection.Imp_etat_vote.rf_equal
  let no_match = effective_collection.Imp_etat_vote.rf_no_match
  let parse = effective_collection.Imp_etat_vote.rf_parse
  let different = effective_collection.Imp_etat_vote.rf_different
  let element = effective_collection.Imp_etat_vote.rf_element
  let range_match = effective_collection.Imp_etat_vote.rf_range_match
  let partial_match = effective_collection.Imp_etat_vote.rf_partial_match
  let perfect_match = effective_collection.Imp_etat_vote.rf_perfect_match
  let print = effective_collection.Imp_etat_vote.rf_print
  end ;;

