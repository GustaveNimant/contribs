module Diag_2oo3 =
  struct
  end ;;

module Imp_diag_2oo3 =
  struct
  type ('e0_T, 'c1_T, 'abst_T) me_as_species = {
    (* From species pair#Imp_pair. *)
    rf_constr : 'c1_T -> 'e0_T -> 'abst_T ;
    (* From species pair#Imp_pair. *)
    rf_equal : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species basics#Basic_object. *)
    rf_parse : Basics._focty_string -> 'abst_T ;
    (* From species basics#Basic_object. *)
    rf_print : 'abst_T -> Basics._focty_string ;
    (* From species pair#Imp_pair. *)
    rf_prj_a : 'abst_T -> 'c1_T ;
    (* From species pair#Imp_pair. *)
    rf_prj_b : 'abst_T -> 'e0_T ;
    (* From species pair#Imp_pair. *)
    rf_element : 'abst_T ;
    (* From species sets#Setoid. *)
    rf_different : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species diag#Imp_diag_2oo3. *)
    rf_valid : 'abst_T -> Basics._focty_bool ;
    }
  let valid _p_E_equal _p_E_partial_match _p_E_perfect_match _p_E_range_match
    abst_prj_b (x : 'abst_T) =
    (Basics._bar__bar_ (_p_E_equal (abst_prj_b x) _p_E_range_match)
      (Basics._bar__bar_ (_p_E_equal (abst_prj_b x) _p_E_partial_match)
        (_p_E_equal (abst_prj_b x) _p_E_perfect_match)))
  (* Fully defined 'Imp_diag_2oo3' species's collection generator. *)
  let collection_create () _p_C_element _p_C_equal _p_E_element _p_E_equal
    _p_E_partial_match _p_E_perfect_match _p_E_range_match =
    (* From species pair#Imp_pair. *)
    let local_constr = Pair.Imp_pair.constr in
    (* From species pair#Imp_pair. *)
    let local_equal = Pair.Imp_pair.equal _p_C_equal _p_E_equal in
    (* From species basics#Basic_object. *)
    let local_parse = Basics.Basic_object.parse in
    (* From species basics#Basic_object. *)
    let local_print = Basics.Basic_object.print in
    (* From species pair#Imp_pair. *)
    let local_prj_a = Pair.Imp_pair.prj_a in
    (* From species pair#Imp_pair. *)
    let local_prj_b = Pair.Imp_pair.prj_b in
    (* From species pair#Imp_pair. *)
    let local_element = Pair.Imp_pair.element _p_C_element _p_E_element
      local_constr in
    (* From species sets#Setoid. *)
    let local_different = Sets.Setoid.different local_equal in
    (* From species diag#Imp_diag_2oo3. *)
    let local_valid = valid _p_E_equal _p_E_partial_match _p_E_perfect_match
      _p_E_range_match local_prj_b in
    { rf_constr = local_constr ;
      rf_equal = local_equal ;
      rf_parse = local_parse ;
      rf_print = local_print ;
      rf_prj_a = local_prj_a ;
      rf_prj_b = local_prj_b ;
      rf_element = local_element ;
      rf_different = local_different ;
      rf_valid = local_valid ;
       }
    
  end ;;

