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
  x=`egrep '^species ' $i | egrep -v '_S \(|_S|_subtype '` 
  if [ "$x" != "" ]
  then
    echo "No _S in file $i : $x"
  fi
done