module Full =
  struct
  type 'abst_T me_as_species = {
    (* From species full#Full. *)
    rf_create_some_value : Basics._focty_int ;
    (* From species full#Full. *)
    rf_double : 'abst_T -> Basics._focty_int ;
    (* From species full#Full. *)
    rf_print : 'abst_T -> Basics._focty_unit ;
    }
  let create_some_value = 42
  let double (x : 'abst_T) = (Basics._plus_ x x)
  let print (x : 'abst_T) = (Basics.print_int x)
  (* Fully defined 'Full' species's collection generator. *)
  let collection_create () =
    (* From species full#Full. *)
    let local_create_some_value = create_some_value in
    (* From species full#Full. *)
    let local_double = double in
    (* From species full#Full. *)
    let local_print = print in
    { rf_create_some_value = local_create_some_value ;
      rf_double = local_double ;
      rf_print = local_print ;
       }
    
  end ;;

module type Full_collectionSig = sig
  type me_as_carrier
  (* From species full#Full. *)
  val create_some_value : Basics._focty_int
  (* From species full#Full. *)
  val double : me_as_carrier -> Basics._focty_int
  (* From species full#Full. *)
  val print : me_as_carrier -> Basics._focty_unit
  end

module Full_collection : Full_collectionSig =
  struct
  (* Carrier's structure explicitly given by "rep". *)
  type me_as_carrier = Basics._focty_int
  let effective_collection =
    Full.collection_create ()
  let create_some_value = effective_collection.Full.rf_create_some_value
  let double = effective_collection.Full.rf_double
  let print = effective_collection.Full.rf_print
  end ;;

(Basics.print_string "\nUn nombre entier au hasard ")
;;
let v = Full.create_some_value
;;
(Basics.print_int v)
;;
(Basics.print_string "\n")
;;
