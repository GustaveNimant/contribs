#!/bin/bash

args=$@
argnumber=$#
script=`basename $0`

if [ $# -lt 1 ]
then
    echo -e "Usage :\n${script} <file>\n"
    exit;
fi 

sed -e 's/^-- /-- InH: /' $1 > ${1}.save
mv  ${1}.save $1
echo "git diff $1"