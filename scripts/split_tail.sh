#!/bin/bash
cd `dirname "${BASH_SOURCE[0]}"`
cd ..

if [ "$#" -ne 2 ]; then
    echo "Usage: scripts/split_tail.sh number_of_chunks working_directory"
    exit 1
fi

split -d "--number=l/$1" "$2/tail.icnf" "$2/seg" --additional-suffix=.icnf

find "$2" -type f -name 'seg*.icnf' -print | while read filename; do
    echo "$filename"
    cat "$2/head.icnf" "$filename" > "$2/temp.icnf"
    mv "$2/temp.icnf" "$filename"
done
