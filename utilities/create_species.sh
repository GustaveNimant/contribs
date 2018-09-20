#!/bin/bash

args=$@
argnumber=$#
script=`basename $0`

if [ $# -lt 1 ]
then
    echo -e "Usage :\n${script} <file>\n"
    exit;
fi 

if [ `echo ${1} | grep -c '_S'` == "0" ]
then
    species="${1}_S"
else
    species="${1}"
fi

file="${species}.fcl"
rm -f $file
echo "création du fichier $file"

echo 'open "basics";;' >> $file
echo ' ' >> $file

if [ $# -eq 2 ]
then
    inherit=$2
    echo -e "open \"$inherit\";;\n" >> $file
fi 

echo "species $species (" >> $file
echo ' ' >> $file
echo ') =' >> $file
echo ' ' >> $file

if [ $# -eq 2 ]
then
    inherit=$2
    echo -e "  inherit $inherit;\n" >> $file
fi 

echo "end;;" >> $file
exit