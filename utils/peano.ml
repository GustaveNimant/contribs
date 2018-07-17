module Peano =
  struct
  end ;;

module Imp_peano =
  struct
  type 'abst_T me_as_species = {
    (* From species peano#Imp_peano. *)
    rf_diff : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species peano#Imp_peano. *)
    rf_equal : 'abst_T -> 'abst_T -> Basics._focty_bool ;
    (* From species peano#Imp_peano. *)
    rf_s : 'abst_T -> 'abst_T ;
    (* From species peano#Imp_peano. *)
    rf_zero : 'abst_T ;
    }
  let diff (x : 'abst_T) (y : 'abst_T) =
    if (Basics._equal_ x y) then false else true
  let equal (x : 'abst_T) (y : 'abst_T) = (Basics._equal_ x y)
  let s (x : 'abst_T) = (Basics.int_succ x)
  let zero = 0
  (* Fully defined 'Imp_peano' species's collection generator. *)
  let collection_create () =
    (* From species peano#Imp_peano. *)
    let local_diff = diff in
    (* From species peano#Imp_peano. *)
    let local_equal = equal in
    (* From species peano#Imp_peano. *)
    let local_s = s in
    (* From species peano#Imp_peano. *)
    let local_zero = zero in
    { rf_diff = local_diff ;
      rf_equal = local_equal ;
      rf_s = local_s ;
      rf_zero = local_zero ;
       }
    
  end ;;

module type Coll_peanoSig = sig
  type me_as_carrier
  (* From species peano#Imp_peano. *)
  val diff : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species peano#Imp_peano. *)
  val equal : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species peano#Imp_peano. *)
  val s : me_as_carrier -> me_as_carrier
  (* From species peano#Imp_peano. *)
  val zero : me_as_carrier
  end

module Coll_peano : Coll_peanoSig =
  struct
  (* Carrier's structure explicitly given by "rep". *)
  type me_as_carrier = Basics._focty_int
  let effective_collection =
    Imp_peano.collection_create ()
  let diff = effective_collection.Imp_peano.rf_diff
  let equal = effective_collection.Imp_peano.rf_equal
  let s = effective_collection.Imp_peano.rf_s
  let zero = effective_collection.Imp_peano.rf_zero
  end ;;

module Peano_Arith =
  struct
  end ;;

