module Finite_Set_S =
  struct
  let element abst_empty = abst_empty
  let equal abst_subset (x : 'abst_T) (y : 'abst_T) =
    (Basics._amper__amper_ (abst_subset x y) (abst_subset y x))
  end ;;

