#!/usr/bin/env python

import copy
import os.path

class Stats(object):
    ANNOTS = ['code', 'annot', 'inv', 'harness']
    FIELDS = ['l', 'a', 'rw', 'vc'] + ANNOTS + ['dafny_t']

    def __init__(self, l=0, a=0, rw=0, vc=0, code=0, annot=0, inv=0, harness=0, dafny_t=0):
        self.l  = l
        self.a  = a
        self.rw = rw
        self.vc = vc
        # ------------------------
        self.code    = code
        self.annot   = annot
        self.inv     = inv
        self.harness = harness
        # ------------------------
        self.dafny_t = dafny_t
        
    def column_values(self):
        return [('\\#L',        "%4s",  self.l), 
                ('\\#A*',       "%4s",  self.a), 
                ('RW (s)',      "%6s",  self.rw), 
                ('VC (s)',      "%6s",  self.vc),
                ('\\#L',        "%4s",  self.code), 
                ('\\#A (\\#I)', "%10s", "%d (%d)" % (self.annot + self.inv, self.inv)),
                ('Ver (s)',     "%9s",  self.dafny_t)]

    def header(self):
        return " & ".join(map(lambda (k,fmt,v): "\\textbf{%s}" % k, self.column_values()))

    def row(self):
        return " & ".join(map(lambda (k,fmt,v): fmt % str(v), self.column_values()))

    def __str__(self):
        return ", ".join(map(lambda k: "%s = %s" % (k, self[k]), self.FIELDS))

    def __getitem__(self, key):
        assert key in self.FIELDS
        return self.__dict__[key]

    def __setitem__(self, key, item): 
        assert key in self.FIELDS
        self.__dict__[key] = item
        
    def __add__(self, obj):
        r = copy.deepcopy(self)
        for k in self.FIELDS:
            r[k] = self[k] + obj[k]
        return r

    def __iadd__(self, d2):
        return self + d2
    
    def fields(self):
        return self.__dict__.keys()

NAME_FMT = "%-20s"

FILES = [('kv_cnt.dfy',
          'Key-Value Store',
          Stats(l=36, a=4, rw=0.02, vc=0.02)),

         ('twophase_cnt.dfy',
          'Two-Phase Commit',
          Stats(l=33, a=4, rw=0.09, vc=0.02, dafny_t=12.81)),

         ('raft_cnt.dfy',
          'Raft Leader Election',
          Stats(l=54, a=12, rw=0.05, vc=0.03, dafny_t=301.68)),

         ('paxos_cnt.dfy',
          'Single-Decree Paxos',
          Stats(l=87, a=44, rw=1.66, vc=0.39))]

stat_total = Stats()

print " & ".join(["", stat_total.header()]), '\\\\'
print "\\midrule"

for (filename, name, stat) in FILES:
    if not os.path.isfile(filename):
        print " & ".join([NAME_FMT % name, stat.row()]), '\\\\'
        stat_total += stat
        continue

    with open(filename, 'r') as f:
        for line in f:
            l = line.rstrip()
            for c in Stats.ANNOTS:
                if l.endswith("// " + c):
                    stat[c] += 1
                    break
                
        print " & ".join([NAME_FMT % name, stat.row()]), '\\\\'
        stat_total += stat

print "\\midrule"
print " & ".join([NAME_FMT % "\\textbf{Total}", stat_total.row()]), '\\\\'
