#!/bin/bash

args=$@
argnumber=$#
script=`basename $0`

if [ $# -lt 1 ]
then
    echo -e "Usage :\n${script} <file> ... <file>\n"
    exit;
fi 

echo "FOCALIZE_SRC=\\" > files_fcl.mk
for i in $args
do
    ok=`echo $i | grep -c '.fcl'`
    if [ "$ok" == "0" ]
    then
	echo "  $i.fcl \\" >> files_fcl.mk
    else
	echo "  $i \\" >> files_fcl.mk
    fi
done
echo "" >> files_fcl.mk

make clean; make
exit;

