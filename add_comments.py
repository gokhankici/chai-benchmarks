#!/usr/bin/env python

import sys
import fileinput
import argparse

parser = argparse.ArgumentParser(description='Process some integers.')
parser.add_argument('files', metavar='FILE', type=str, nargs='+',
                    help='list of files to read from')
parser.add_argument('--tag', type=str, default='code',
                    help='default tag to append to each line')
parser.add_argument('--comment', type=str, default='//',
                    help='single line comment delimiter')

args = parser.parse_args()

files = args.files

assert max([len(line.rstrip()) for line in fileinput.input(files)]) < 120

for line in fileinput.input(files):
    l = line.rstrip()
    if len(l.lstrip()) == 0:
        print l
    else:
        print "%-120s %s %s" % (l, args.comment, args.tag)
