module Un_Etre_humain_S =
  struct
  let est_un_adulte abst_age (s : 'abst_T) = (Basics._gt__equal_ abst_age 18)
  let est_un_mineur abst_age (s : 'abst_T) = (Basics._lt_ abst_age 18)
  end ;;

