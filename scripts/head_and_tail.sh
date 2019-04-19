#!/bin/bash
cd `dirname "${BASH_SOURCE[0]}"`
cd ..

if [ "$#" -ne 1 ]; then
    echo "Usage: scripts/head_and_tail.sh working_directory"
    exit 1
fi

if [ ! -f compiled/march_cc ]; then
    echo "Installing march_cc..."
    bash "installers/add_march.sh"
fi

echo 'Running march_cc...'
compiled/march_cc "$1/simplified.cnf"

echo 'Copying files...'
# We randomise the order of cubes in the tail file:
cat "/tmp/cubes" | shuf > "$1/tail.icnf"

echo 'p inccnf' > "$1/head.icnf"
cat "$1/simplified.cnf" | grep -v c >> "$1/head.icnf"
cat "/tmp/learnt" >> "$1/head.icnf"

cat "$1/head.icnf" "$1/tail.icnf" > "$1/full.icnf"
