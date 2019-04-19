#!/bin/bash
cd `dirname "${BASH_SOURCE[0]}"`
cd ..
set -e

# Update Armin Biere's lingeling submodule:
git submodule update --init

cd lingeling
./configure.sh
make
cp *ngeling ../compiled
make clean
cd -

echo 'Installed lingeling'
