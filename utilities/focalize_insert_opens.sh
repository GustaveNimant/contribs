#!/bin/bash

args=$@
argnumber=$#
script=`basename $0`

if [ $# -lt 1 ]
then
    echo -e "Usage :\n${script} <heritage_file> <focalize_file>\n"
    exit;
fi 

file=$1
focalize_open_list.pl $file > opens
delete_lines_where.pl 'open "' $file 

cat opens $file > new_file
mv new_file  $file
