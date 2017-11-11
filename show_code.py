#!/usr/bin/env python

import fileinput

tag = '// code'

for line in fileinput.input():
    if line.startswith(tag) or tag not in line:
        continue

    print line.replace(tag, "").rstrip()
