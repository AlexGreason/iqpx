#!/bin/bash
cd "$( dirname "${BASH_SOURCE[0]}" )"
cd ..

if [ ! -f compiled/iglucose ]; then
    echo "Installing iglucose..."
    bash "installers/add_iglucose.sh"
fi

compiled/iglucose "$@"
