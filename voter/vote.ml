module Voteur =
  struct
  let sensor _p_P_prj_a (diag : 'p3_T) = (_p_P_prj_a diag)
  let state _p_P_prj_b (diag : 'p3_T) = (_p_P_prj_b diag)
  end ;;

module Imp_vote =
  struct
  let voter _p_E_no_match _p_E_partial_match _p_E_perfect_match
    _p_E_range_match _p_C_capt_1 _p_C_capt_2 _p_C_capt_3
    _p_V_consistency_rule _p_P_constr (v1 : 'v2_T) (v2 : 'v2_T)
    (v3 : 'v2_T) = let c1 = (_p_V_consistency_rule v1 v2)
    in
    let c2 = (_p_V_consistency_rule v1 v3)
    in
    let c3 = (_p_V_consistency_rule v2 v3)
    in
    if c1
      then if c2
             then if c3
                    then (v1, (_p_P_constr _p_C_capt_1 _p_E_perfect_match))
                    else (v1, (_p_P_constr _p_C_capt_1 _p_E_partial_match))
             else if c3
                    then (v2, (_p_P_constr _p_C_capt_2 _p_E_partial_match))
                    else (v1, (_p_P_constr _p_C_capt_3 _p_E_range_match))
      else if c2
             then if c3
                    then (v3, (_p_P_constr _p_C_capt_3 _p_E_partial_match))
                    else (v3, (_p_P_constr _p_C_capt_2 _p_E_range_match))
             else if c3 then (v2, (_p_P_constr _p_C_capt_1 _p_E_range_match))
                    else (v1, (_p_P_constr _p_C_capt_1 _p_E_no_match))
  end ;;

