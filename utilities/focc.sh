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
    if [ `echo $i | grep -c '.fcl'` != "0" ]
    then
	echo "  $i \\" >> files_fcl.mk
    else
	if [ `echo $i | grep -c '\.'` != "0" ]
	then
	    echo "  ${i}fcl \\" >> files_fcl.mk
	else
	    if [ `echo $i | grep -c '_S'` != "0" ]
	    then
		echo "  ${i}.fcl \\" >> files_fcl.mk
	    else
		echo "  ${i}_S.fcl \\" >> files_fcl.mk
	    fi
	fi
    fi
done
echo "" >> files_fcl.mk

rm build.bin;make
exit;

