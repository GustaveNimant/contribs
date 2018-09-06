#!/bin/bash

args=$@
argnumber=$#
script=`basename $0`

if [ $# -lt 1 ]
then
    echo -e "Usage :\n${script} <focalize_file>\n"
    exit;
fi 

file=$1
delete_lines_where.pl '  UScr is Un_Scrutin_S,' $file
insert_file_after.pl '  UTer is Un_Territoire_S,' uscr $file 