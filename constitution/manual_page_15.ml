module Setoid_product =
  struct
  let element _p_A_element _p_B_element abst_pair =
    (abst_pair _p_A_element _p_B_element)
  let _equal_ _p_A_equal _p_B_equal abst_fst abst_snd (x : 'abst_T)
    (y : 'abst_T) =
    (Basics._amper__amper_ (_p_A_equal (abst_fst x) (abst_fst y))
      (_p_B_equal (abst_snd x) (abst_snd y)))
  end ;;

