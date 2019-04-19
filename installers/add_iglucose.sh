#!/bin/bash
cd `dirname "${BASH_SOURCE[0]}"`
cd ..
set -e

# Update iglucose submodule:
git submodule update --init

cd iglucose/core
make
cp iglucose ../../compiled/iglucose
make clean
cd -

echo 'Installed iglucose'
