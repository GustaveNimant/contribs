module Setoid =
  struct
  let different abst__equal_ (x : 'abst_T) (y : 'abst_T) =
    (Basics._tilda__tilda_ (abst__equal_ x y))
  end ;;

