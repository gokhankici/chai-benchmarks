#!/bin/bash

if [[ $# -ne 1 ]]; then
    echo "usage: $0 <.dfy file>" >&2
    exit 1
fi

filename=$(basename $1)

if [[ -f $1 ]]; then
    rsync -aP $1 goto:dafny_codes/
else
    echo "'$1' does not exists" >&2
    exit 1
fi

