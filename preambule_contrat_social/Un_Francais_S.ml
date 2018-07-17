module Un_Francais_S =
  struct
  let est_un_francais (s : 'abst_T) = true
  let habite_un_territoire_francais _p_UTfr_est_un_territoire_francais
    abst_habite_un_territoire (fra : 'abst_T) (ter : 'uTfr0_T) =
    (Basics._amper__amper_ (abst_habite_un_territoire fra ter)
      (_p_UTfr_est_un_territoire_francais ter))
  end ;;

