module type Coll_diagSig = sig
  type me_as_carrier
  (* From species pair#Imp_pair. *)
  val constr : Num_capteur.Coll_capteur.me_as_carrier ->
                 Etat_vote.Coll_etat_vote.me_as_carrier -> me_as_carrier
  (* From species pair#Imp_pair. *)
  val equal : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species basics#Basic_object. *)
  val parse : Basics._focty_string -> me_as_carrier
  (* From species basics#Basic_object. *)
  val print : me_as_carrier -> Basics._focty_string
  (* From species pair#Imp_pair. *)
  val prj_a : me_as_carrier -> Num_capteur.Coll_capteur.me_as_carrier
  (* From species pair#Imp_pair. *)
  val prj_b : me_as_carrier -> Etat_vote.Coll_etat_vote.me_as_carrier
  (* From species pair#Imp_pair. *)
  val element : me_as_carrier
  (* From species sets#Setoid. *)
  val different : me_as_carrier -> me_as_carrier -> Basics._focty_bool
  (* From species diag#Imp_diag_2oo3. *)
  val valid : me_as_carrier -> Basics._focty_bool
  end

module Coll_diag : Coll_diagSig =
  struct
  (* Carrier's structure explicitly given by "rep". *)
  type me_as_carrier =
    Num_capteur.Coll_capteur.me_as_carrier *
      Etat_vote.Coll_etat_vote.me_as_carrier
  let effective_collection =
    Diag.Imp_diag_2oo3.collection_create () Num_capteur.Coll_capteur.element
    Num_capteur.Coll_capteur.equal Etat_vote.Coll_etat_vote.element
    Etat_vote.Coll_etat_vote.equal Etat_vote.Coll_etat_vote.partial_match
    Etat_vote.Coll_etat_vote.perfect_match
    Etat_vote.Coll_etat_vote.range_match
  let constr = effective_collection.Diag.Imp_diag_2oo3.rf_constr
  let equal = effective_collection.Diag.Imp_diag_2oo3.rf_equal
  let parse = effective_collection.Diag.Imp_diag_2oo3.rf_parse
  let print = effective_collection.Diag.Imp_diag_2oo3.rf_print
  let prj_a = effective_collection.Diag.Imp_diag_2oo3.rf_prj_a
  let prj_b = effective_collection.Diag.Imp_diag_2oo3.rf_prj_b
  let element = effective_collection.Diag.Imp_diag_2oo3.rf_element
  let different = effective_collection.Diag.Imp_diag_2oo3.rf_different
  let valid = effective_collection.Diag.Imp_diag_2oo3.rf_valid
  end ;;

module Sp_int_imp_vote_tol =
  struct
  type 'abst_T me_as_species = {
    (* From species gen_vote#Gen_voter. *)
    rf_diag : Value.Coll_int_imp_value_tol.me_as_carrier *
                Coll_diag.me_as_carrier -> Coll_diag.me_as_carrier ;
    (* From species vote#Voteur. *)
    rf_sensor : Coll_diag.me_as_carrier ->
                  Num_capteur.Coll_capteur.me_as_carrier ;
    (* From species vote#Voteur. *)
    rf_state : Coll_diag.me_as_carrier ->
                 Etat_vote.Coll_etat_vote.me_as_carrier ;
    (* From species gen_vote#Gen_voter. *)
    rf_value : Value.Coll_int_imp_value_tol.me_as_carrier *
                 Coll_diag.me_as_carrier ->
                 Value.Coll_int_imp_value_tol.me_as_carrier ;
    (* From species vote#Imp_vote. *)
    rf_voter : Value.Coll_int_imp_value_tol.me_as_carrier ->
                 Value.Coll_int_imp_value_tol.me_as_carrier ->
                   Value.Coll_int_imp_value_tol.me_as_carrier ->
                     Value.Coll_int_imp_value_tol.me_as_carrier *
                       Coll_diag.me_as_carrier ;
    }
  (* Fully defined 'Sp_int_imp_vote_tol' species's collection generator. *)
  let collection_create () =
    (* From species gen_vote#Gen_voter. *)
    let local_diag = Gen_vote.Gen_voter.diag in
    (* From species vote#Voteur. *)
    let local_sensor = Vote.Voteur.sensor Coll_diag.prj_a in
    (* From species vote#Voteur. *)
    let local_state = Vote.Voteur.state Coll_diag.prj_b in
    (* From species gen_vote#Gen_voter. *)
    let local_value = Gen_vote.Gen_voter.value in
    (* From species vote#Imp_vote. *)
    let local_voter = Vote.Imp_vote.voter Etat_vote.Coll_etat_vote.no_match
      Etat_vote.Coll_etat_vote.partial_match
      Etat_vote.Coll_etat_vote.perfect_match
      Etat_vote.Coll_etat_vote.range_match Num_capteur.Coll_capteur.capt_1
      Num_capteur.Coll_capteur.capt_2 Num_capteur.Coll_capteur.capt_3
      Value.Coll_int_imp_value_tol.consistency_rule Coll_diag.constr in
    { rf_diag = local_diag ;
      rf_sensor = local_sensor ;
      rf_state = local_state ;
      rf_value = local_value ;
      rf_voter = local_voter ;
       }
    
  end ;;

module type Coll_int_imp_vote_tolSig = sig
  type me_as_carrier
  (* From species gen_vote#Gen_voter. *)
  val diag : Value.Coll_int_imp_value_tol.me_as_carrier *
               Coll_diag.me_as_carrier -> Coll_diag.me_as_carrier
  (* From species vote#Voteur. *)
  val sensor : Coll_diag.me_as_carrier ->
                 Num_capteur.Coll_capteur.me_as_carrier
  (* From species vote#Voteur. *)
  val state : Coll_diag.me_as_carrier ->
                Etat_vote.Coll_etat_vote.me_as_carrier
  (* From species gen_vote#Gen_voter. *)
  val value : Value.Coll_int_imp_value_tol.me_as_carrier *
                Coll_diag.me_as_carrier ->
                Value.Coll_int_imp_value_tol.me_as_carrier
  (* From species vote#Imp_vote. *)
  val voter : Value.Coll_int_imp_value_tol.me_as_carrier ->
                Value.Coll_int_imp_value_tol.me_as_carrier ->
                  Value.Coll_int_imp_value_tol.me_as_carrier ->
                    Value.Coll_int_imp_value_tol.me_as_carrier *
                      Coll_diag.me_as_carrier
  end

module Coll_int_imp_vote_tol : Coll_int_imp_vote_tolSig =
  struct
  (* Carrier's structure explicitly given by "rep". *)
  type me_as_carrier = Basics._focty_unit
  let effective_collection =
    Sp_int_imp_vote_tol.collection_create ()
  let diag = effective_collection.Sp_int_imp_vote_tol.rf_diag
  let sensor = effective_collection.Sp_int_imp_vote_tol.rf_sensor
  let state = effective_collection.Sp_int_imp_vote_tol.rf_state
  let value = effective_collection.Sp_int_imp_vote_tol.rf_value
  let voter = effective_collection.Sp_int_imp_vote_tol.rf_voter
  end ;;

let p_int_tol (x : Basics._focty_string) =
  (Value.Coll_int_imp_value_tol.parse x)
;;
let voter_value_int_tol (v1 : Basics._focty_string)
  (v2 : Basics._focty_string) (v3 : Basics._focty_string) =
  let s =
    (Coll_int_imp_vote_tol.value
      (Coll_int_imp_vote_tol.voter (p_int_tol v1) (p_int_tol v2)
        (p_int_tol v3)))
  in
  (Value.Coll_int_imp_value_tol.print s)
;;
let voter_etat_int_tol (v1 : Basics._focty_string)
  (v2 : Basics._focty_string) (v3 : Basics._focty_string) =
  let s =
    (Coll_int_imp_vote_tol.diag
      (Coll_int_imp_vote_tol.voter (p_int_tol v1) (p_int_tol v2)
        (p_int_tol v3)))
  in
  (Etat_vote.Coll_etat_vote.print (Coll_int_imp_vote_tol.state s))
;;
let voter_val_int_tol (v1 : Basics._focty_string) (v2 : Basics._focty_string)
  (v3 : Basics._focty_string) =
  let s =
    (Coll_int_imp_vote_tol.diag
      (Coll_int_imp_vote_tol.voter (p_int_tol v1) (p_int_tol v2)
        (p_int_tol v3)))
  in
  (Num_capteur.Coll_capteur.print (Coll_int_imp_vote_tol.sensor s))
;;
let va10 = "1"
;;
let va20 = "3"
;;
let va30 = "5"
;;
(Basics.print_string "Voteur entier avec tolerance de 2\n")
;;
(Basics.print_string "v1 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value_tol.print (p_int_tol va10)))
;;
(Basics.print_string ", v2 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value_tol.print (p_int_tol va20)))
;;
(Basics.print_string ", v3 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value_tol.print (p_int_tol va30)))
;;
(Basics.print_string " --> val : ")
;;
(Basics.print_string (voter_value_int_tol va10 va20 va30))
;;
(Basics.print_string " , diag : (")
;;
(Basics.print_string (voter_val_int_tol va10 va20 va30))
;;
(Basics.print_string ", ")
;;
(Basics.print_string (voter_etat_int_tol va10 va20 va30))
;;
(Basics.print_string ")\n")
;;
let va11 = "1"
;;
let va21 = "1"
;;
let va31 = "5"
;;
(Basics.print_string "v1 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value_tol.print (p_int_tol va11)))
;;
(Basics.print_string ", v2 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value_tol.print (p_int_tol va21)))
;;
(Basics.print_string ", v3 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value_tol.print (p_int_tol va31)))
;;
(Basics.print_string " --> val : ")
;;
(Basics.print_string (voter_value_int_tol va11 va21 va31))
;;
(Basics.print_string " , diag : (")
;;
(Basics.print_string (voter_val_int_tol va11 va21 va31))
;;
(Basics.print_string ", ")
;;
(Basics.print_string (voter_etat_int_tol va11 va21 va31))
;;
(Basics.print_string ")\n")
;;
let va12 = "4"
;;
let va22 = "5"
;;
let va32 = "5"
;;
(Basics.print_string "v1 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value_tol.print (p_int_tol va12)))
;;
(Basics.print_string ", v2 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value_tol.print (p_int_tol va22)))
;;
(Basics.print_string ", v3 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value_tol.print (p_int_tol va32)))
;;
(Basics.print_string " --> val : ")
;;
(Basics.print_string (voter_value_int_tol va12 va22 va32))
;;
(Basics.print_string " , diag : (")
;;
(Basics.print_string (voter_val_int_tol va12 va22 va32))
;;
(Basics.print_string ", ")
;;
(Basics.print_string (voter_etat_int_tol va12 va22 va32))
;;
(Basics.print_string ")\n")
;;
let va14 = "1"
;;
let va24 = "4"
;;
let va34 = "7"
;;
(Basics.print_string "v1 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value_tol.print (p_int_tol va14)))
;;
(Basics.print_string ", v2 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value_tol.print (p_int_tol va24)))
;;
(Basics.print_string ", v3 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value_tol.print (p_int_tol va34)))
;;
(Basics.print_string " --> val : ")
;;
(Basics.print_string (voter_value_int_tol va14 va24 va34))
;;
(Basics.print_string " , diag : (")
;;
(Basics.print_string (voter_val_int_tol va14 va24 va34))
;;
(Basics.print_string ", ")
;;
(Basics.print_string (voter_etat_int_tol va14 va24 va34))
;;
(Basics.print_string ")\n")
;;
module Sp_int_imp_vote =
  struct
  type 'abst_T me_as_species = {
    (* From species gen_vote#Gen_voter. *)
    rf_diag : Value.Coll_int_imp_value.me_as_carrier *
                Coll_diag.me_as_carrier -> Coll_diag.me_as_carrier ;
    (* From species vote#Voteur. *)
    rf_sensor : Coll_diag.me_as_carrier ->
                  Num_capteur.Coll_capteur.me_as_carrier ;
    (* From species vote#Voteur. *)
    rf_state : Coll_diag.me_as_carrier ->
                 Etat_vote.Coll_etat_vote.me_as_carrier ;
    (* From species gen_vote#Gen_voter. *)
    rf_value : Value.Coll_int_imp_value.me_as_carrier *
                 Coll_diag.me_as_carrier ->
                 Value.Coll_int_imp_value.me_as_carrier ;
    (* From species vote#Imp_vote. *)
    rf_voter : Value.Coll_int_imp_value.me_as_carrier ->
                 Value.Coll_int_imp_value.me_as_carrier ->
                   Value.Coll_int_imp_value.me_as_carrier ->
                     Value.Coll_int_imp_value.me_as_carrier *
                       Coll_diag.me_as_carrier ;
    }
  (* Fully defined 'Sp_int_imp_vote' species's collection generator. *)
  let collection_create () =
    (* From species gen_vote#Gen_voter. *)
    let local_diag = Gen_vote.Gen_voter.diag in
    (* From species vote#Voteur. *)
    let local_sensor = Vote.Voteur.sensor Coll_diag.prj_a in
    (* From species vote#Voteur. *)
    let local_state = Vote.Voteur.state Coll_diag.prj_b in
    (* From species gen_vote#Gen_voter. *)
    let local_value = Gen_vote.Gen_voter.value in
    (* From species vote#Imp_vote. *)
    let local_voter = Vote.Imp_vote.voter Etat_vote.Coll_etat_vote.no_match
      Etat_vote.Coll_etat_vote.partial_match
      Etat_vote.Coll_etat_vote.perfect_match
      Etat_vote.Coll_etat_vote.range_match Num_capteur.Coll_capteur.capt_1
      Num_capteur.Coll_capteur.capt_2 Num_capteur.Coll_capteur.capt_3
      Value.Coll_int_imp_value.consistency_rule Coll_diag.constr in
    { rf_diag = local_diag ;
      rf_sensor = local_sensor ;
      rf_state = local_state ;
      rf_value = local_value ;
      rf_voter = local_voter ;
       }
    
  end ;;

module type Coll_int_imp_voteSig = sig
  type me_as_carrier
  (* From species gen_vote#Gen_voter. *)
  val diag : Value.Coll_int_imp_value.me_as_carrier * Coll_diag.me_as_carrier
               -> Coll_diag.me_as_carrier
  (* From species vote#Voteur. *)
  val sensor : Coll_diag.me_as_carrier ->
                 Num_capteur.Coll_capteur.me_as_carrier
  (* From species vote#Voteur. *)
  val state : Coll_diag.me_as_carrier ->
                Etat_vote.Coll_etat_vote.me_as_carrier
  (* From species gen_vote#Gen_voter. *)
  val value : Value.Coll_int_imp_value.me_as_carrier *
                Coll_diag.me_as_carrier ->
                Value.Coll_int_imp_value.me_as_carrier
  (* From species vote#Imp_vote. *)
  val voter : Value.Coll_int_imp_value.me_as_carrier ->
                Value.Coll_int_imp_value.me_as_carrier ->
                  Value.Coll_int_imp_value.me_as_carrier ->
                    Value.Coll_int_imp_value.me_as_carrier *
                      Coll_diag.me_as_carrier
  end

module Coll_int_imp_vote : Coll_int_imp_voteSig =
  struct
  (* Carrier's structure explicitly given by "rep". *)
  type me_as_carrier = Basics._focty_unit
  let effective_collection =
    Sp_int_imp_vote.collection_create ()
  let diag = effective_collection.Sp_int_imp_vote.rf_diag
  let sensor = effective_collection.Sp_int_imp_vote.rf_sensor
  let state = effective_collection.Sp_int_imp_vote.rf_state
  let value = effective_collection.Sp_int_imp_vote.rf_value
  let voter = effective_collection.Sp_int_imp_vote.rf_voter
  end ;;

let p_int (x : Basics._focty_string) = (Value.Coll_int_imp_value.parse x)
;;
let voter_value_int (v1 : Basics._focty_string) (v2 : Basics._focty_string)
  (v3 : Basics._focty_string) =
  let s =
    (Coll_int_imp_vote.value
      (Coll_int_imp_vote.voter (p_int v1) (p_int v2) (p_int v3)))
  in
  (Value.Coll_int_imp_value.print s)
;;
let voter_etat_int (v1 : Basics._focty_string) (v2 : Basics._focty_string)
  (v3 : Basics._focty_string) =
  let s =
    (Coll_int_imp_vote.diag
      (Coll_int_imp_vote.voter (p_int v1) (p_int v2) (p_int v3)))
  in
  (Etat_vote.Coll_etat_vote.print (Coll_int_imp_vote.state s))
;;
let voter_val_int (v1 : Basics._focty_string) (v2 : Basics._focty_string)
  (v3 : Basics._focty_string) =
  let s =
    (Coll_int_imp_vote.diag
      (Coll_int_imp_vote.voter (p_int v1) (p_int v2) (p_int v3)))
  in
  (Num_capteur.Coll_capteur.print (Coll_int_imp_vote.sensor s))
;;
let vb10 = "1"
;;
let vb20 = "3"
;;
let vb30 = "5"
;;
(Basics.print_string "Voteur entier sans tolerance\n")
;;
(Basics.print_string "v1 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value.print (p_int vb10)))
;;
(Basics.print_string ", v2 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value.print (p_int vb20)))
;;
(Basics.print_string ", v3 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value.print (p_int vb30)))
;;
(Basics.print_string " --> val : ")
;;
(Basics.print_string (voter_value_int vb10 vb20 vb30))
;;
(Basics.print_string " , diag : (")
;;
(Basics.print_string (voter_val_int vb10 vb20 vb30))
;;
(Basics.print_string ", ")
;;
(Basics.print_string (voter_etat_int vb10 vb20 vb30))
;;
(Basics.print_string ")\n")
;;
let vb11 = "5"
;;
let vb21 = "5"
;;
let vb31 = "5"
;;
(Basics.print_string "v1 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value.print (p_int vb11)))
;;
(Basics.print_string ", v2 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value.print (p_int vb21)))
;;
(Basics.print_string ", v3 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value.print (p_int vb31)))
;;
(Basics.print_string " --> val : ")
;;
(Basics.print_string (voter_value_int vb11 vb21 vb31))
;;
(Basics.print_string " , diag : (")
;;
(Basics.print_string (voter_val_int vb11 vb21 vb31))
;;
(Basics.print_string ", ")
;;
(Basics.print_string (voter_etat_int vb11 vb21 vb31))
;;
(Basics.print_string ")\n")
;;
let vb12 = "4"
;;
let vb22 = "5"
;;
let vb32 = "5"
;;
(Basics.print_string "v1 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value.print (p_int vb12)))
;;
(Basics.print_string ", v2 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value.print (p_int vb22)))
;;
(Basics.print_string ", v3 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value.print (p_int vb32)))
;;
(Basics.print_string " --> val : ")
;;
(Basics.print_string (voter_value_int vb12 vb22 vb32))
;;
(Basics.print_string " , diag : (")
;;
(Basics.print_string (voter_val_int vb12 vb22 vb32))
;;
(Basics.print_string ", ")
;;
(Basics.print_string (voter_etat_int vb12 vb22 vb32))
;;
(Basics.print_string ")\n")
;;
let vb14 = "1"
;;
let vb24 = "4"
;;
let vb34 = "7"
;;
(Basics.print_string "v1 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value.print (p_int vb14)))
;;
(Basics.print_string ", v2 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value.print (p_int vb24)))
;;
(Basics.print_string ", v3 : ")
;;
(Basics.print_string (Value.Coll_int_imp_value.print (p_int vb34)))
;;
(Basics.print_string " --> val : ")
;;
(Basics.print_string (voter_value_int vb14 vb24 vb34))
;;
(Basics.print_string " , diag : (")
;;
(Basics.print_string (voter_val_int vb14 vb24 vb34))
;;
(Basics.print_string ", ")
;;
(Basics.print_string (voter_etat_int vb14 vb24 vb34))
;;
(Basics.print_string ")\n")
;;
module Sp_bool_imp_vote =
  struct
  type 'abst_T me_as_species = {
    (* From species gen_vote#Gen_voter. *)
    rf_diag : Value.Coll_bool_imp_value.me_as_carrier *
                Coll_diag.me_as_carrier -> Coll_diag.me_as_carrier ;
    (* From species vote#Voteur. *)
    rf_sensor : Coll_diag.me_as_carrier ->
                  Num_capteur.Coll_capteur.me_as_carrier ;
    (* From species vote#Voteur. *)
    rf_state : Coll_diag.me_as_carrier ->
                 Etat_vote.Coll_etat_vote.me_as_carrier ;
    (* From species gen_vote#Gen_voter. *)
    rf_value : Value.Coll_bool_imp_value.me_as_carrier *
                 Coll_diag.me_as_carrier ->
                 Value.Coll_bool_imp_value.me_as_carrier ;
    (* From species vote#Imp_vote. *)
    rf_voter : Value.Coll_bool_imp_value.me_as_carrier ->
                 Value.Coll_bool_imp_value.me_as_carrier ->
                   Value.Coll_bool_imp_value.me_as_carrier ->
                     Value.Coll_bool_imp_value.me_as_carrier *
                       Coll_diag.me_as_carrier ;
    }
  (* Fully defined 'Sp_bool_imp_vote' species's collection generator. *)
  let collection_create () =
    (* From species gen_vote#Gen_voter. *)
    let local_diag = Gen_vote.Gen_voter.diag in
    (* From species vote#Voteur. *)
    let local_sensor = Vote.Voteur.sensor Coll_diag.prj_a in
    (* From species vote#Voteur. *)
    let local_state = Vote.Voteur.state Coll_diag.prj_b in
    (* From species gen_vote#Gen_voter. *)
    let local_value = Gen_vote.Gen_voter.value in
    (* From species vote#Imp_vote. *)
    let local_voter = Vote.Imp_vote.voter Etat_vote.Coll_etat_vote.no_match
      Etat_vote.Coll_etat_vote.partial_match
      Etat_vote.Coll_etat_vote.perfect_match
      Etat_vote.Coll_etat_vote.range_match Num_capteur.Coll_capteur.capt_1
      Num_capteur.Coll_capteur.capt_2 Num_capteur.Coll_capteur.capt_3
      Value.Coll_bool_imp_value.consistency_rule Coll_diag.constr in
    { rf_diag = local_diag ;
      rf_sensor = local_sensor ;
      rf_state = local_state ;
      rf_value = local_value ;
      rf_voter = local_voter ;
       }
    
  end ;;

module type Coll_bool_imp_voteSig = sig
  type me_as_carrier
  (* From species gen_vote#Gen_voter. *)
  val diag : Value.Coll_bool_imp_value.me_as_carrier *
               Coll_diag.me_as_carrier -> Coll_diag.me_as_carrier
  (* From species vote#Voteur. *)
  val sensor : Coll_diag.me_as_carrier ->
                 Num_capteur.Coll_capteur.me_as_carrier
  (* From species vote#Voteur. *)
  val state : Coll_diag.me_as_carrier ->
                Etat_vote.Coll_etat_vote.me_as_carrier
  (* From species gen_vote#Gen_voter. *)
  val value : Value.Coll_bool_imp_value.me_as_carrier *
                Coll_diag.me_as_carrier ->
                Value.Coll_bool_imp_value.me_as_carrier
  (* From species vote#Imp_vote. *)
  val voter : Value.Coll_bool_imp_value.me_as_carrier ->
                Value.Coll_bool_imp_value.me_as_carrier ->
                  Value.Coll_bool_imp_value.me_as_carrier ->
                    Value.Coll_bool_imp_value.me_as_carrier *
                      Coll_diag.me_as_carrier
  end

module Coll_bool_imp_vote : Coll_bool_imp_voteSig =
  struct
  (* Carrier's structure explicitly given by "rep". *)
  type me_as_carrier = Basics._focty_unit
  let effective_collection =
    Sp_bool_imp_vote.collection_create ()
  let diag = effective_collection.Sp_bool_imp_vote.rf_diag
  let sensor = effective_collection.Sp_bool_imp_vote.rf_sensor
  let state = effective_collection.Sp_bool_imp_vote.rf_state
  let value = effective_collection.Sp_bool_imp_vote.rf_value
  let voter = effective_collection.Sp_bool_imp_vote.rf_voter
  end ;;

let p_bool (x : Basics._focty_string) = (Value.Coll_bool_imp_value.parse x)
;;
let voter_value_bool (v1 : Basics._focty_string) (v2 : Basics._focty_string)
  (v3 : Basics._focty_string) =
  let s =
    (Coll_bool_imp_vote.value
      (Coll_bool_imp_vote.voter (p_bool v1) (p_bool v2) (p_bool v3)))
  in
  (Value.Coll_bool_imp_value.print s)
;;
let voter_etat_bool (v1 : Basics._focty_string) (v2 : Basics._focty_string)
  (v3 : Basics._focty_string) =
  let s =
    (Coll_bool_imp_vote.diag
      (Coll_bool_imp_vote.voter (p_bool v1) (p_bool v2) (p_bool v3)))
  in
  (Etat_vote.Coll_etat_vote.print (Coll_bool_imp_vote.state s))
;;
let voter_val_bool (v1 : Basics._focty_string) (v2 : Basics._focty_string)
  (v3 : Basics._focty_string) =
  let s =
    (Coll_bool_imp_vote.diag
      (Coll_bool_imp_vote.voter (p_bool v1) (p_bool v2) (p_bool v3)))
  in
  (Num_capteur.Coll_capteur.print (Coll_bool_imp_vote.sensor s))
;;
let va13 = "False"
;;
let va23 = "Falsee"
;;
let va33 = "True"
;;
(Basics.print_string "Voteur booleen sans tolerance\n")
;;
(Basics.print_string "v1 : ")
;;
(Basics.print_string (Value.Coll_bool_imp_value.print (p_bool va13)))
;;
(Basics.print_string ", v2 : ")
;;
(Basics.print_string (Value.Coll_bool_imp_value.print (p_bool va23)))
;;
(Basics.print_string ", v3 : ")
;;
(Basics.print_string (Value.Coll_bool_imp_value.print (p_bool va33)))
;;
(Basics.print_string " --> val : ")
;;
(Basics.print_string (voter_value_bool va13 va23 va33))
;;
(Basics.print_string " , diag : (")
;;
(Basics.print_string (voter_val_bool va13 va23 va33))
;;
(Basics.print_string ", ")
;;
(Basics.print_string (voter_etat_bool va13 va23 va33))
;;
(Basics.print_string ")\n")
;;
let va15 = "False"
;;
let va25 = "False"
;;
let va35 = "False"
;;
(Basics.print_string "v1 : ")
;;
(Basics.print_string (Value.Coll_bool_imp_value.print (p_bool va15)))
;;
(Basics.print_string ", v2 : ")
;;
(Basics.print_string (Value.Coll_bool_imp_value.print (p_bool va25)))
;;
(Basics.print_string ", v3 : ")
;;
(Basics.print_string (Value.Coll_bool_imp_value.print (p_bool va35)))
;;
(Basics.print_string " --> val : ")
;;
(Basics.print_string (voter_value_bool va15 va25 va35))
;;
(Basics.print_string " , diag : (")
;;
(Basics.print_string (voter_val_bool va15 va25 va35))
;;
(Basics.print_string ", ")
;;
(Basics.print_string (voter_etat_bool va15 va25 va35))
;;
(Basics.print_string ")\n")
;;
let p_bool2 (x : Basics._focty_string) = (Value.Coll_bool_imp_value.parse x)
;;
let voter_etat_bool2 (v1 : Basics._focty_string) (v2 : Basics._focty_string)
  (v3 : Basics._focty_string) =
  let s =
    (Coll_bool_imp_vote.diag
      (Coll_bool_imp_vote.voter (p_bool2 v1) (p_bool2 v2) (p_bool2 v3)))
  in
  (Etat_vote.Coll_etat_vote.print (Coll_bool_imp_vote.state s))
;;
let voter_val_bool2 (v1 : Basics._focty_string) (v2 : Basics._focty_string)
  (v3 : Basics._focty_string) =
  let s =
    (Coll_bool_imp_vote.diag
      (Coll_bool_imp_vote.voter (p_bool2 v1) (p_bool2 v2) (p_bool2 v3)))
  in
  (Num_capteur.Coll_capteur.print (Coll_bool_imp_vote.sensor s))
;;
let va16 = "False"
;;
let va26 = "Falsee"
;;
let va36 = "True"
;;
(Basics.print_string "v1 : ")
;;
(Basics.print_string (Value.Coll_bool_imp_value.print (p_bool2 va16)))
;;
(Basics.print_string ", v2 : ")
;;
(Basics.print_string (Value.Coll_bool_imp_value.print (p_bool2 va26)))
;;
(Basics.print_string ", v3 : ")
;;
(Basics.print_string (Value.Coll_bool_imp_value.print (p_bool2 va36)))
;;
(Basics.print_string " --> val : ")
;;
(Basics.print_string (voter_value_bool va16 va26 va36))
;;
(Basics.print_string " , diag : (")
;;
(Basics.print_string (voter_val_bool va16 va26 va36))
;;
(Basics.print_string ", ")
;;
(Basics.print_string (voter_etat_bool va16 va26 va36))
;;
(Basics.print_string ")\n")
;;
let va17 = "False"
;;
let va27 = "False"
;;
let va37 = "False"
;;
(Basics.print_string "v1 : ")
;;
(Basics.print_string (Value.Coll_bool_imp_value.print (p_bool2 va17)))
;;
(Basics.print_string ", v2 : ")
;;
(Basics.print_string (Value.Coll_bool_imp_value.print (p_bool2 va27)))
;;
(Basics.print_string ", v3 : ")
;;
(Basics.print_string (Value.Coll_bool_imp_value.print (p_bool2 va37)))
;;
(Basics.print_string " --> val : ")
;;
(Basics.print_string (voter_value_bool va17 va27 va37))
;;
(Basics.print_string " , diag : (")
;;
(Basics.print_string (voter_val_bool va17 va27 va37))
;;
(Basics.print_string ", ")
;;
(Basics.print_string (voter_etat_bool va17 va27 va37))
;;
(Basics.print_string ")\n")
;;
module Sp_int_value_with_value_imp_vote =
  struct
  type 'abst_T me_as_species = {
    (* From species gen_vote#Gen_voter. *)
    rf_diag : Value_with_valid.Coll_int_value_with_valid.me_as_carrier *
                Coll_diag.me_as_carrier -> Coll_diag.me_as_carrier ;
    (* From species vote#Voteur. *)
    rf_sensor : Coll_diag.me_as_carrier ->
                  Num_capteur.Coll_capteur.me_as_carrier ;
    (* From species vote#Voteur. *)
    rf_state : Coll_diag.me_as_carrier ->
                 Etat_vote.Coll_etat_vote.me_as_carrier ;
    (* From species gen_vote#Gen_voter. *)
    rf_value : Value_with_valid.Coll_int_value_with_valid.me_as_carrier *
                 Coll_diag.me_as_carrier ->
                 Value_with_valid.Coll_int_value_with_valid.me_as_carrier ;
    (* From species vote#Imp_vote. *)
    rf_voter : Value_with_valid.Coll_int_value_with_valid.me_as_carrier ->
                 Value_with_valid.Coll_int_value_with_valid.me_as_carrier ->
                   Value_with_valid.Coll_int_value_with_valid.me_as_carrier
                     ->
                     Value_with_valid.Coll_int_value_with_valid.me_as_carrier
                        * Coll_diag.me_as_carrier ;
    }
  (* Fully defined 'Sp_int_value_with_value_imp_vote' species's collection generator. *)
  let collection_create () =
    (* From species gen_vote#Gen_voter. *)
    let local_diag = Gen_vote.Gen_voter.diag in
    (* From species vote#Voteur. *)
    let local_sensor = Vote.Voteur.sensor Coll_diag.prj_a in
    (* From species vote#Voteur. *)
    let local_state = Vote.Voteur.state Coll_diag.prj_b in
    (* From species gen_vote#Gen_voter. *)
    let local_value = Gen_vote.Gen_voter.value in
    (* From species vote#Imp_vote. *)
    let local_voter = Vote.Imp_vote.voter Etat_vote.Coll_etat_vote.no_match
      Etat_vote.Coll_etat_vote.partial_match
      Etat_vote.Coll_etat_vote.perfect_match
      Etat_vote.Coll_etat_vote.range_match Num_capteur.Coll_capteur.capt_1
      Num_capteur.Coll_capteur.capt_2 Num_capteur.Coll_capteur.capt_3
      Value_with_valid.Coll_int_value_with_valid.consistency_rule
      Coll_diag.constr in
    { rf_diag = local_diag ;
      rf_sensor = local_sensor ;
      rf_state = local_state ;
      rf_value = local_value ;
      rf_voter = local_voter ;
       }
    
  end ;;

module type Coll_int_value_with_valid_imp_voteSig = sig
  type me_as_carrier
  (* From species gen_vote#Gen_voter. *)
  val diag : Value_with_valid.Coll_int_value_with_valid.me_as_carrier *
               Coll_diag.me_as_carrier -> Coll_diag.me_as_carrier
  (* From species vote#Voteur. *)
  val sensor : Coll_diag.me_as_carrier ->
                 Num_capteur.Coll_capteur.me_as_carrier
  (* From species vote#Voteur. *)
  val state : Coll_diag.me_as_carrier ->
                Etat_vote.Coll_etat_vote.me_as_carrier
  (* From species gen_vote#Gen_voter. *)
  val value : Value_with_valid.Coll_int_value_with_valid.me_as_carrier *
                Coll_diag.me_as_carrier ->
                Value_with_valid.Coll_int_value_with_valid.me_as_carrier
  (* From species vote#Imp_vote. *)
  val voter : Value_with_valid.Coll_int_value_with_valid.me_as_carrier ->
                Value_with_valid.Coll_int_value_with_valid.me_as_carrier ->
                  Value_with_valid.Coll_int_value_with_valid.me_as_carrier ->
                    Value_with_valid.Coll_int_value_with_valid.me_as_carrier
                       * Coll_diag.me_as_carrier
  end

module Coll_int_value_with_valid_imp_vote : Coll_int_value_with_valid_imp_voteSig =
  struct
  (* Carrier's structure explicitly given by "rep". *)
  type me_as_carrier = Basics._focty_unit
  let effective_collection =
    Sp_int_value_with_value_imp_vote.collection_create ()
  let diag = effective_collection.Sp_int_value_with_value_imp_vote.rf_diag
  let sensor =
    effective_collection.Sp_int_value_with_value_imp_vote.rf_sensor
  let state = effective_collection.Sp_int_value_with_value_imp_vote.rf_state
  let value = effective_collection.Sp_int_value_with_value_imp_vote.rf_value
  let voter = effective_collection.Sp_int_value_with_value_imp_vote.rf_voter
  end ;;

let p_val (x : Basics._focty_string) (y : Basics._focty_string) =
  (Value_with_valid.Coll_int_value_with_valid.parse2 x y)
;;
let voter_value_int_value_with_valid
  (v1 : Value_with_valid.Coll_int_value_with_valid.me_as_carrier)
  (v2 : Value_with_valid.Coll_int_value_with_valid.me_as_carrier)
  (v3 : Value_with_valid.Coll_int_value_with_valid.me_as_carrier) =
  let s =
    (Coll_int_value_with_valid_imp_vote.value
      (Coll_int_value_with_valid_imp_vote.voter v1 v2 v3))
  in
  (Value_with_valid.Coll_int_value_with_valid.print s)
;;
let voter_etat_int_value_with_valid
  (v1 : Value_with_valid.Coll_int_value_with_valid.me_as_carrier)
  (v2 : Value_with_valid.Coll_int_value_with_valid.me_as_carrier)
  (v3 : Value_with_valid.Coll_int_value_with_valid.me_as_carrier) =
  let s =
    (Coll_int_value_with_valid_imp_vote.diag
      (Coll_int_value_with_valid_imp_vote.voter v1 v2 v3))
  in
  (Etat_vote.Coll_etat_vote.print
    (Coll_int_value_with_valid_imp_vote.state s))
;;
let voter_val_int_value_with_valid
  (v1 : Value_with_valid.Coll_int_value_with_valid.me_as_carrier)
  (v2 : Value_with_valid.Coll_int_value_with_valid.me_as_carrier)
  (v3 : Value_with_valid.Coll_int_value_with_valid.me_as_carrier) =
  let s =
    (Coll_int_value_with_valid_imp_vote.diag
      (Coll_int_value_with_valid_imp_vote.voter v1 v2 v3))
  in
  (Num_capteur.Coll_capteur.print
    (Coll_int_value_with_valid_imp_vote.sensor s))
;;
let va113 = "23"
;;
let va123 = "45"
;;
let va133 = "23"
;;
let vali = "valid"
;;
let invali = "invalid"
;;
let p_parse2 (x : Basics._focty_string) (y : Basics._focty_string) =
  (Value_with_valid.Coll_int_value_with_valid.parse2 x y)
;;
(Basics.print_string "Voteur entier avec validit\233\n")
;;
(Basics.print_string "v1 : ")
;;
(Basics.print_string
  (Value_with_valid.Coll_int_value_with_valid.print (p_parse2 va113 vali)))
;;
(Basics.print_string ", v2 : ")
;;
(Basics.print_string
  (Value_with_valid.Coll_int_value_with_valid.print (p_parse2 va123 vali)))
;;
(Basics.print_string ", v3 : ")
;;
(Basics.print_string
  (Value_with_valid.Coll_int_value_with_valid.print (p_parse2 va133 vali)))
;;
(Basics.print_string " --> val : ")
;;
(Basics.print_string
  (voter_value_int_value_with_valid (p_parse2 va113 vali)
    (p_parse2 va123 vali) (p_parse2 va133 vali)))
;;
(Basics.print_string " , diag : (")
;;
(Basics.print_string
  (voter_val_int_value_with_valid (p_parse2 va113 vali) (p_parse2 va123 vali)
    (p_parse2 va133 vali)))
;;
(Basics.print_string ", ")
;;
(Basics.print_string
  (voter_etat_int_value_with_valid (p_parse2 va113 vali)
    (p_parse2 va123 vali) (p_parse2 va133 vali)))
;;
(Basics.print_string ")\n")
;;
(Basics.print_string "v1 : ")
;;
(Basics.print_string
  (Value_with_valid.Coll_int_value_with_valid.print (p_parse2 va113 invali)))
;;
(Basics.print_string ", v2 : ")
;;
(Basics.print_string
  (Value_with_valid.Coll_int_value_with_valid.print (p_parse2 va123 vali)))
;;
(Basics.print_string ", v3 : ")
;;
(Basics.print_string
  (Value_with_valid.Coll_int_value_with_valid.print (p_parse2 va133 vali)))
;;
(Basics.print_string " --> val : ")
;;
(Basics.print_string
  (voter_value_int_value_with_valid (p_parse2 va113 invali)
    (p_parse2 va123 vali) (p_parse2 va133 vali)))
;;
(Basics.print_string " , diag : (")
;;
(Basics.print_string
  (voter_val_int_value_with_valid (p_parse2 va113 invali)
    (p_parse2 va123 vali) (p_parse2 va133 vali)))
;;
(Basics.print_string ", ")
;;
(Basics.print_string
  (voter_etat_int_value_with_valid (p_parse2 va113 invali)
    (p_parse2 va123 vali) (p_parse2 va133 vali)))
;;
(Basics.print_string ")\n")
;;
(Basics.print_string "v1 : ")
;;
(Basics.print_string
  (Value_with_valid.Coll_int_value_with_valid.print (p_parse2 va113 invali)))
;;
(Basics.print_string ", v2 : ")
;;
(Basics.print_string
  (Value_with_valid.Coll_int_value_with_valid.print (p_parse2 va123 invali)))
;;
(Basics.print_string ", v3 : ")
;;
(Basics.print_string
  (Value_with_valid.Coll_int_value_with_valid.print (p_parse2 va133 vali)))
;;
(Basics.print_string " --> val : ")
;;
(Basics.print_string
  (voter_value_int_value_with_valid (p_parse2 va113 invali)
    (p_parse2 va123 vali) (p_parse2 va133 vali)))
;;
(Basics.print_string " , diag : (")
;;
(Basics.print_string
  (voter_val_int_value_with_valid (p_parse2 va113 invali)
    (p_parse2 va123 vali) (p_parse2 va133 vali)))
;;
(Basics.print_string ", ")
;;
(Basics.print_string
  (voter_etat_int_value_with_valid (p_parse2 va113 invali)
    (p_parse2 va123 vali) (p_parse2 va133 vali)))
;;
(Basics.print_string ")\n")
;;
