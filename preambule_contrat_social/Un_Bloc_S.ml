module Un_Bloc_S =
  struct
  let l_ordinal_est_non_negatif abst_l_ordinal (blo : 'abst_T) =
    (Basics._gt__equal_ (abst_l_ordinal blo) 0)
  let l_ordinal_est_positif abst_l_ordinal (blo : 'abst_T) =
    (Basics._gt_ (abst_l_ordinal blo) 0)
  end ;;

