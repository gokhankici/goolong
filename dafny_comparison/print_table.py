#!/usr/bin/env python

import copy
import os.path as op

NAME_FMT = "%-20s"

class FileStats(object):
    ANNOTS = ['code', 'annot', 'inv', 'harness']

    def __init__(self, code=0, annot=0, inv=0, harness=0, comment='//'):
        self.code    = code
        self.annot   = annot
        self.inv     = inv
        self.harness = harness
        self.comment = comment
        
    def __str__(self):
        return ", ".join(map(lambda k: "%s = %s" % (k, self[k]), self.ANNOTS))

    def __getitem__(self, key):
        assert key in self.ANNOTS
        return self.__dict__[key]

    def __setitem__(self, key, item): 
        assert key in self.ANNOTS
        self.__dict__[key] = item
        
    def __add__(self, obj):
        r = copy.deepcopy(self)
        for k in self.ANNOTS:
            r[k] = self[k] + obj[k]
        return r

    def __iadd__(self, d2):
        return self + d2

class GlobalStats(object):
    FIELDS = ['icet_stats', 'dafny_stats']

    def __init__(self, icet_rw=0, icet_vc=0, dafny_t=0):
        self.icet_stats  = FileStats(comment='%%')
        self.icet_rw     = icet_rw
        self.icet_vc     = icet_vc
        self.dafny_stats = FileStats(comment='//')
        self.dafny_t     = dafny_t
        
    def column_values(self):
        return [('# Lines'  ,  "%10s",  self.icet_stats.code), 
                ('# Anns'   ,  "%10s", "%d" % (self.icet_stats.annot)),
                ('# Invs'   ,  "%10s", "%d" % (self.icet_stats.inv)),
                ('# Lines'  ,  "%10s",  self.dafny_stats.code), 
                ('# Anns'   ,  "%10s", "%d" % (self.dafny_stats.annot)),
                ('# Invs'   ,  "%10s", "%d" % (self.dafny_stats.inv)),
                ('# Harness',  "%10s",  self.dafny_stats.harness)
                ]

    def header(self):
        return " | ".join(map(lambda (k,fmt,v): "%-10s" % k, self.column_values()))

    def row(self):
        return " | ".join(map(lambda (k,fmt,v): fmt % str(v), self.column_values()))

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

def update_stats(filename, stat):
    if not op.isfile(filename):
        return

    with open(filename, 'r') as f:
        for line in f:
            l = line.rstrip()
            for c in FileStats.ANNOTS:
                if l.endswith("%s %s" % (stat.comment, c)):
                    stat[c] += 1
                    break

if __name__ == '__main__':
    THIS_FOLDER   = op.dirname(op.abspath(op.realpath(__file__)))
    ICET_FOLDER   = op.join(THIS_FOLDER, 'icet')
    DAFNY_FOLDER  = op.join(THIS_FOLDER, 'dafny')

    FILES = [(('twophase.icet', 'twophase.dfy'),
            'Two-Phase Commit',
            GlobalStats()),

            (('raft.icet', 'raft.dfy'),
            'Raft Leader Election',
            GlobalStats()),

            (('paxos.icet', 'paxos.dfy'),
            'Single-Decree Paxos',
            GlobalStats())]
    
    stat_total = GlobalStats()

    print " | ".join([" " * 20, "%-36s" % "IceT", "%-49s" % "Dafny"])
    print " " * 20, "-" * 90
    print " | ".join(["%-20s" % "Name", stat_total.header()])
    print "-" * 111

    for ((icet_filename, dafny_filename), name, both_stat) in FILES:
        update_stats(op.join(ICET_FOLDER,  icet_filename),  both_stat.icet_stats)
        update_stats(op.join(DAFNY_FOLDER, dafny_filename), both_stat.dafny_stats)

        print " | ".join([NAME_FMT % name, both_stat.row()])
        stat_total += both_stat

    print "-" * 111
    print " | ".join([NAME_FMT % "Total", stat_total.row()])
