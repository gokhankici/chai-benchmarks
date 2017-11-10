#!/usr/bin/env python

import copy
import os.path

class Stats(object):
    def __str__(self):
        return ", ".join(map(lambda k: "%s = %s" % (k, self[k]), self.FIELDS))
    
    def header(self):
        return " & ".join(map(lambda (k,fmt,v): fmt % k, self.column_values()))

    def row(self):
        return " & ".join(map(lambda (k,fmt,v): fmt % str(v), self.column_values()))

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

class IceTStats(Stats):
    FIELDS = ['l', 'a', 'rw', 'vc']

    def __init__(self, l=0, a=0, rw=0, vc=0):
        self.l  = l
        self.a  = a
        self.rw = rw
        self.vc = vc
        
    def column_values(self):
        return [('#L',     "%3s", self.l), 
                ('#A*',    "%3s", self.a), 
                ('RW (s)', "%6s", self.rw), 
                ('VC (s)', "%6s", self.vc)]

class DafnyStats(Stats):
    FIELDS = ['code', 'annot', 'inv', 'harness']

    def __init__(self, code=0, annot=0, inv=0, harness=0):
        self.code    = code
        self.annot   = annot
        self.inv     = inv
        self.harness = harness
        
    def column_values(self):
        return [('#L',      "%3s", self.code), 
                ('#A #(I)', "%9s", "%d (%d)" % (self.annot + self.inv, self.inv))]

    
NAME_FMT = "%-20s"

FILES = [('kv_cnt.dfy',       'Key-Value Store',      IceTStats(36, 4, 0.02, 0.02)),
         ('twophase_cnt.dfy', 'Two-Phase Commit',     IceTStats(33, 4, 0.09, 0.02)),
         ('raft_cnt.dfy',     'Raft Leader Election', IceTStats(54, 12, 0.05, 0.03)),
         ('paxos_cnt.dfy',    'Single-Decree Paxos',  IceTStats(87, 44, 1.66, 0.39))]

icet_total  = IceTStats()
dafny_total = DafnyStats()

print " & ".join([NAME_FMT % "Benchmarks", icet_total.header(), dafny_total.header()]), '\\\\'

for (filename, name, icet) in FILES:
    icet_total += icet

    if not os.path.isfile(filename):
        print " & ".join([NAME_FMT % name, icet.row()]), '\\\\'
        continue

    with open(filename, 'r') as f:
        d = DafnyStats()

        for line in f:
            l = line.rstrip()
            for c in DafnyStats.FIELDS:
                if l.endswith("// " + c):
                    d[c] += 1
                    break
                
        dafny_total += d
        print " & ".join([NAME_FMT % name, icet.row(), d.row()]), '\\\\'

print " & ".join([NAME_FMT % "Total", icet_total.row(), dafny_total.row()]), '\\\\'
