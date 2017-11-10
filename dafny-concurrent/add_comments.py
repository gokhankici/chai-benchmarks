#!/usr/bin/env python

import sys
import fileinput

# print max([len(line.rstrip()) for line in fileinput.input()])
# sys.exit(0)

for line in fileinput.input():
    l = line.rstrip()
    if len(l.lstrip()) == 0:
        print l
    else:
        print "%-120s // code" % (l)
