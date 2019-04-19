#!/bin/bash
cd `dirname "${BASH_SOURCE[0]}"`
cd ..

TIMEOUT=60

if [ "$#" -lt 2 ]; then
    echo "Usage: scripts/preprocess.sh input_file.cnf output_directory [timeout_seconds]"
    exit 1
fi

if [ "$#" -gt 2 ]; then
    TIMEOUT=$3
fi

if [ ! -f compiled/lingeling ]; then
    echo "Installing lingeling..."
    bash "installers/add_lingeling.sh"
fi

echo 'Creating target directory...'
mkdir "$2"

echo "Running lingeling for a maximum of $TIMEOUT seconds..."
compiled/lingeling "$1" -s -T "$TIMEOUT" -o "$2/simplified.cnf" | tee "$2/lingeling.log"

# Really weirdly, lingeling prints an extra 'c ' when unknown:
status=`grep -E '^(c )+s ' "$2/lingeling.log" | grep -o '[A-Z]*'`

echo "$status" > "$2/simp_status.txt"

printf "Status: \033[32;1m$status\033[0m\n"

if [ "${status:0:3}" == "SAT" ]; then
    grep -E '^c v ' "$2/lingeling.log" | sed 'sic v ii' > "$2/solution.txt"
fi
