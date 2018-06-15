type _focty_bintree_t = 
  | Leaf
  | Node of (_focty_bintree_t * Basics._focty_int * _focty_bintree_t) ;;
let rec mirror (t : _focty_bintree_t) =
  match t with
   | Leaf ->
       (begin
       Leaf
       end)
   | Node (l, i, r) ->
       (begin
       (Node ((mirror r), i, (mirror l)))
       end)
;;
