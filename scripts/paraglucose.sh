#!/bin/bash
cd `dirname "${BASH_SOURCE[0]}"`
cd ..

if [ "$#" -ne 2 ]; then
    echo "Usage: scripts/paraglucose.sh number_of_cores working_directory"
    exit 1
fi

if [ ! -f compiled/iglucose ]; then
    echo "Installing iglucose..."
    bash "installers/add_iglucose.sh"
fi

find "$2" -type f -name 'seg*.icnf' -print | while read filename; do
    outfile=$(echo $filename | rev | sed 's/fnci/gol/' | rev)
    echo "compiled/iglucose $filename $outfile > /dev/null ; echo \"Created $outfile\""
done > "$2/pjobs.out"

cat "$2/pjobs.out" | parallel -P "$1"
