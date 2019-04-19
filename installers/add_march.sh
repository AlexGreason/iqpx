#!/bin/bash
cd `dirname "${BASH_SOURCE[0]}"`
cd ..
set -e

# wget http://www.st.ewi.tudelft.nl/~marijn/march_cc.tar.gz
cp installers/march_cc.tar.gz march_cc.tar.gz
tar xzvf march_cc.tar.gz
cd march_cc
# rm ._*
# sed -i 's/^inline //' *
make
cd -

cp march_cc/march_cc compiled/march_cc
rm -rf march_cc
rm march_cc.tar.gz

echo 'Installed march_cc'
