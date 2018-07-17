module Gen_basic_type =
  struct
  end ;;

module Gen_basic_type_tol =
  struct
  end ;;

module Int_value =
  struct
  type 'abst_T me_as_species = {
    (* From species basic_type#Int_value. *)
    rf_element : 'abst_T ;
    (* From species basic_type#Int_value. *)
    rf_equal : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species basic_type#Int_value. *)
    rf_geq : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species basic_type#Int_value. *)
    rf_of_int : Basics._focty_int -> 'abst_T ;
    (* From species basic_type#Int_value. *)
    rf_parse : Basics._focty_string -> 'abst_T ;
    (* From species basic_type#Int_value. *)
    rf_plus : 'abst_T -> 'abst_T -> 'abst_T ;
    (* From species basic_type#Int_value. *)
    rf_pos : 'abst_T -> Basics._focty_bool ;
    (* From species basic_type#Int_value. *)
    rf_print : 'abst_T -> Basics._focty_string ;
    (* From species sets#Setoid. *)
    rf_different : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    }
  let element = 1
  let equal (x : 'abst_T) (y : 'abst_T) = (Basics.syntactic_equal x y)
  let geq (n1 : 'abst_T) (n2 : 'abst_T) = (Basics._gt__equal_ n1 n2)
  let of_int (n : Basics._focty_int) = n
  let parse (x : Basics._focty_string) = (Basics.int_of_string x)
  let plus (n1 : 'abst_T) (n2 : 'abst_T) = (Basics._plus_ n1 n2)
  let pos (n : 'abst_T) = (Basics._gt_ n 0)
  let print (x : 'abst_T) = (Basics.string_of_int x)
  (* Fully defined 'Int_value' species's collection generator. *)
  let collection_create () =
    (* From species basic_type#Int_value. *)
    let local_element = element in
    (* From species basic_type#Int_value. *)
    let local_equal = equal in
    (* From species basic_type#Int_value. *)
    let local_geq = geq in
    (* From species basic_type#Int_value. *)
    let local_of_int = of_int in
    (* From species basic_type#Int_value. *)
    let local_parse = parse in
    (* From species basic_type#Int_value. *)
    let local_plus = plus in
    (* From species basic_type#Int_value. *)
    let local_pos = pos in
    (* From species basic_type#Int_value. *)
    let local_print = print in
    (* From species sets#Setoid. *)
    let local_different = Sets.Setoid.different local_equal in
    { rf_element = local_element ;
      rf_equal = local_equal ;
      rf_geq = local_geq ;
      rf_of_int = local_of_int ;
      rf_parse = local_parse ;
      rf_plus = local_plus ;
      rf_pos = local_pos ;
      rf_print = local_print ;
      rf_different = local_different ;
       }
    
  end ;;

module type Coll_int_valueSig = sig
  type me_as_carrier
  (* From species basic_type#Int_value. *)
  val element : me_as_carrier
  (* From species basic_type#Int_value. *)
  val equal : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species basic_type#Int_value. *)
  val geq : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species basic_type#Int_value. *)
  val of_int : Basics._focty_int -> me_as_carrier
  (* From species basic_type#Int_value. *)
  val parse : Basics._focty_string -> me_as_carrier
  (* From species basic_type#Int_value. *)
  val plus : me_as_carrier -> me_as_carrier -> me_as_carrier
  (* From species basic_type#Int_value. *)
  val pos : me_as_carrier -> Basics._focty_bool
  (* From species basic_type#Int_value. *)
  val print : me_as_carrier -> Basics._focty_string
  (* From species sets#Setoid. *)
  val different : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  end

module Coll_int_value : Coll_int_valueSig =
  struct
  (* Carrier's structure explicitly given by "rep". *)
  type me_as_carrier = Basics._focty_int
  let effective_collection =
    Int_value.collection_create ()
  let element = effective_collection.Int_value.rf_element
  let equal = effective_collection.Int_value.rf_equal
  let geq = effective_collection.Int_value.rf_geq
  let of_int = effective_collection.Int_value.rf_of_int
  let parse = effective_collection.Int_value.rf_parse
  let plus = effective_collection.Int_value.rf_plus
  let pos = effective_collection.Int_value.rf_pos
  let print = effective_collection.Int_value.rf_print
  let different = effective_collection.Int_value.rf_different
  end ;;

module Bool_value =
  struct
  type 'abst_T me_as_species = {
    (* From species basic_type#Bool_value. *)
    rf_element : 'abst_T ;
    (* From species basic_type#Bool_value. *)
    rf_equal : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species basic_type#Bool_value. *)
    rf_of_bool : Basics._focty_bool -> 'abst_T ;
    (* From species basic_type#Bool_value. *)
    rf_parse : Basics._focty_string -> 'abst_T ;
    (* From species sets#Setoid. *)
    rf_different : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species basic_type#Bool_value. *)
    rf_print : 'abst_T -> Basics._focty_string ;
    }
  let element = true
  let equal (x : 'abst_T) (y : 'abst_T) = (Basics.syntactic_equal x y)
  let of_bool (b : Basics._focty_bool) = b
  let parse (x : Basics._focty_string) =
    if (Basics.syntactic_equal x "True") then true else false
  let print abst_equal (x : 'abst_T) =
    if (abst_equal x true) then "True" else "False"
  (* Fully defined 'Bool_value' species's collection generator. *)
  let collection_create () =
    (* From species basic_type#Bool_value. *)
    let local_element = element in
    (* From species basic_type#Bool_value. *)
    let local_equal = equal in
    (* From species basic_type#Bool_value. *)
    let local_of_bool = of_bool in
    (* From species basic_type#Bool_value. *)
    let local_parse = parse in
    (* From species sets#Setoid. *)
    let local_different = Sets.Setoid.different local_equal in
    (* From species basic_type#Bool_value. *)
    let local_print = print local_equal in
    { rf_element = local_element ;
      rf_equal = local_equal ;
      rf_of_bool = local_of_bool ;
      rf_parse = local_parse ;
      rf_different = local_different ;
      rf_print = local_print ;
       }
    
  end ;;

module type Coll_bool_valueSig = sig
  type me_as_carrier
  (* From species basic_type#Bool_value. *)
  val element : me_as_carrier
  (* From species basic_type#Bool_value. *)
  val equal : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species basic_type#Bool_value. *)
  val of_bool : Basics._focty_bool -> me_as_carrier
  (* From species basic_type#Bool_value. *)
  val parse : Basics._focty_string -> me_as_carrier
  (* From species sets#Setoid. *)
  val different : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species basic_type#Bool_value. *)
  val print : me_as_carrier -> Basics._focty_string
  end

module Coll_bool_value : Coll_bool_valueSig =
  struct
  (* Carrier's structure explicitly given by "rep". *)
  type me_as_carrier = Basics._focty_bool
  let effective_collection =
    Bool_value.collection_create ()
  let element = effective_collection.Bool_value.rf_element
  let equal = effective_collection.Bool_value.rf_equal
  let of_bool = effective_collection.Bool_value.rf_of_bool
  let parse = effective_collection.Bool_value.rf_parse
  let different = effective_collection.Bool_value.rf_different
  let print = effective_collection.Bool_value.rf_print
  end ;;

