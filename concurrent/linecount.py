#!/usr/bin/env python

import fileinput

columns = ['code', 'annot', 'harness']

values = {c: 0 for c in columns}

for line in fileinput.input():
    l = line.rstrip()

    for c in columns:
        if l.endswith("// " + c):
            values[c] += 1
            break

for c in columns:
    print "%-10s : %d" % (c, values[c])
