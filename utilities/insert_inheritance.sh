#!/bin/bash

args=$@
argnumber=$#
script=`basename $0`

if [ $# -lt 2 ]
then
    echo -e "Usage :\n${script} <heritage_file> <focalize_file>\n"
    exit;
fi 

heritage=$1
shift;file=$1
echo "heritage $heritage"
delete_lines_where.pl '-- InH:' $file
insert_file_before.pl 'species' $heritage $file
