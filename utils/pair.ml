module Sp_pair =
  struct
  end ;;

module Imp_pair =
  struct
  type ('s10_T, 's21_T, 'abst_T) me_as_species = {
    (* From species pair#Imp_pair. *)
    rf_constr : 's10_T -> 's21_T -> 'abst_T ;
    (* From species pair#Imp_pair. *)
    rf_equal : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species basics#Basic_object. *)
    rf_parse : Basics._focty_string -> 'abst_T ;
    (* From species basics#Basic_object. *)
    rf_print : 'abst_T -> Basics._focty_string ;
    (* From species pair#Imp_pair. *)
    rf_prj_a : 'abst_T -> 's10_T ;
    (* From species pair#Imp_pair. *)
    rf_prj_b : 'abst_T -> 's21_T ;
    (* From species pair#Imp_pair. *)
    rf_element : 'abst_T ;
    (* From species sets#Setoid. *)
    rf_different : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    }
  let constr (n1 : 's10_T) (n2 : 's21_T) = (Basics.pair n1 n2)
  let equal _p_S1_equal _p_S2_equal (n1 : 'abst_T) (n2 : 'abst_T) =
    (Basics._amper__amper_ (_p_S1_equal (Basics.fst n1) (Basics.fst n2))
      (_p_S2_equal (Basics.snd n1) (Basics.snd n2)))
  let prj_a (nn : 'abst_T) = (Basics.fst nn)
  let prj_b (nn : 'abst_T) = (Basics.snd nn)
  let element _p_S1_element _p_S2_element abst_constr =
    (abst_constr _p_S1_element _p_S2_element)
  (* Fully defined 'Imp_pair' species's collection generator. *)
  let collection_create () _p_S2_element _p_S2_equal _p_S1_element
    _p_S1_equal =
    (* From species pair#Imp_pair. *)
    let local_constr = constr in
    (* From species pair#Imp_pair. *)
    let local_equal = equal _p_S1_equal _p_S2_equal in
    (* From species basics#Basic_object. *)
    let local_parse = Basics.Basic_object.parse in
    (* From species basics#Basic_object. *)
    let local_print = Basics.Basic_object.print in
    (* From species pair#Imp_pair. *)
    let local_prj_a = prj_a in
    (* From species pair#Imp_pair. *)
    let local_prj_b = prj_b in
    (* From species pair#Imp_pair. *)
    let local_element = element _p_S1_element _p_S2_element local_constr in
    (* From species sets#Setoid. *)
    let local_different = Sets.Setoid.different local_equal in
    { rf_constr = local_constr ;
      rf_equal = local_equal ;
      rf_parse = local_parse ;
      rf_print = local_print ;
      rf_prj_a = local_prj_a ;
      rf_prj_b = local_prj_b ;
      rf_element = local_element ;
      rf_different = local_different ;
       }
    
  end ;;

