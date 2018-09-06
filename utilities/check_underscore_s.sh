#!/bin/bash

args=$@
argnumber=$#
script=`basename $0`

if [ $# -lt 1 ]
then
    echo -e "Usage :\n${script} <files>\n"
    exit;
fi 

for i in $args
do
  x=`egrep -h '^species |^  inherit' $i | egrep -v '_S \(|_S'` 
  if [ "$x" != "" ]
  then
      string=`echo $x | cut -d" " -f2`
      species=`echo $string | sed 's/;//'`
      if [ "$species" != "Setoid" ]
      then
	  echo "No _S for in file $i : $x"
	  echo "mw $species ${species}_S *.fcl"
      fi
  fi
done