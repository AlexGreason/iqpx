import multiprocessing
import random
import argparse
import signal
import cPickle
import gzip
import time
import sys
import math
import os

from grills import *
from parserle import rle2bin
from velocities import parse_velocity, partial_derivatives
from sys import stdout
from collections import Counter

import subprocess

import numpy as np


class PredecessorSearch(basegrill):

    def __init__(self, g, m, n, padding, setcells, forcerim=True, allunknown=False, oscillator=False, forcefull=True, forcephoenix=False):
        super(PredecessorSearch, self).__init__()
        print("g", g, "m", m, "n", n, "padding", padding)
        self.g = g
        self.m = m
        self.n = n
        self.padding = padding
        self.important_variables = set()

        for t in range(self.g):
            for x in range(m):
                for y in range(n):
                    state = UNKNOWN_VARIABLE_STATE
                    if forcerim:
                        if x < 2 or abs(x - m + 1) < 2:
                            state = DEAD_VARIABLE_STATE
                        if y < 2 or abs(y - n + 1) < 2:
                            state = DEAD_VARIABLE_STATE
                    if t == 0 and (x, y) in setcells:
                        state = setcells[(x, y)]
                    variable = self.apply_state_to_variable(state)
                    self.relate(variable, (t, x, y))
                    if t == 0 and ((x, y) in setcells) or (allunknown and state == UNKNOWN_VARIABLE_STATE):
                        self.important_variables.add(variable)
                    if forcephoenix and t > 0 :
                        self.implies(self.cells[(t - 1, x, y)], -variable)
        if oscillator:
            for x in range(m):
                for y in range(n):
                    self.identify(self.cells[(0, x, y)], self.cells[(g-1, x, y)])
        if forcefull:
            for t in range(1, self.g - 1):
                if (g-1)%t == 0:
                    print("generations", 0, t, "forced to differ")
                    self.forcedifferent(0, t)
        self.enforce_rule()
        print(self.nvars, "variables", len(self.clauses), "clauses")

    def xor(self, var1, var2):
        x = self.newvar()
        self.newclause(var1, var2, -x)
        self.newclause(-var1, var2, x)
        self.newclause(var1, -var2, x)
        self.newclause(-var1, -var2, -x)
        return x

    def forcedifferent(self, gen1, gen2):
        firstgen = []
        secondgen = []
        for c in self.cells:
            if c[0] == gen1:
                firstgen.append((c[1], c[2]))
            if c[0] == gen2:
                secondgen.append((c[1], c[2]))
        diffs = []
        padding = self.padding
        for c in firstgen:
            if c in secondgen:
                if c[0] > padding and abs(c[0] - self.m + 1) > padding and c[1] > padding and abs(c[1] - self.n + 1) > padding:
                    var1 = self.cells[(gen1, c[0], c[1])]
                    var2 = self.cells[(gen2, c[0], c[1])]
                    diffs.append(self.xor(var1, var2))
        if len(diffs) > 0:
            self.newclause(*diffs)

    def notequals(self, var1, var2):
        self.newclause(self.xor(var1, var2))

    def getvariables(self, sol):
        variables = {}
        for s in sol.split():
            try:
                w = int(s)
                variables[abs(w)] = (1 if (w > 0) else 0)
            except ValueError:
                continue
        return variables

    def printsol(self, sol, gen=0):
        variables = self.getvariables(sol)
        for x in range(self.m):
            for y in range(self.n):
                char = "."
                if variables[self.n * x + y + 1 + gen * self.n * self.m] == 1:
                    char = "*"
                sys.stdout.write(char)
            sys.stdout.write("\n")
        sys.stdout.write("\n")

    def getpop(self, sol, gen):
        pop = 0
        variables = self.getvariables(sol)
        for x in range(self.m):
            for y in range(self.n):
                if variables[self.n * x + y + 1 + gen * self.n * self.m] == 1:
                    pop += 1
        return pop

    def exhaust(self, name, prefix, timeout=600, findany=False):
        """
        Find all of the possibilities for the next row after the ones
        provided in the problem. Because iglucose is known to have
        wildly varying times, we cut this short if it exceeds the timeout,
        so it is not guaranteed to be exhaustive unless the timeout exceeds
        the maximum CPU time used by any iglucose instance.
        """

        sol_fifoname = prefix + '.sol'
        cnf_fifoname = prefix + '.icnf'

        if os.path.exists(sol_fifoname):
            os.unlink(sol_fifoname)
        if os.path.exists(cnf_fifoname):
            os.unlink(cnf_fifoname)

        os.mkfifo(sol_fifoname)
        os.mkfifo(cnf_fifoname)

        # Track whether the solver is still running:
        running = True

        satisfied = False
        npreds = 0
        minpop = 9999
        cnf_fifo = open(cnf_fifoname, 'w+')
        run_iglucose(("-cpu-lim=%d" % int(timeout)), cnf_fifoname, sol_fifoname)
        sol_fifo = open(sol_fifoname, 'r')
        stages_completed = 0
        firstsol = None
        minsol = None
        try:
            cnf_fifo.write('p inccnf\n')
            self.write_dimacs(cnf_fifo, write_header=False)

            # Try to extend the partial:
            while running:
                cnf_fifo.write('a 0\n')
                cnf_fifo.flush()
                sol = sol_fifo.readline()
                if sol[:3] == 'SAT':
                    anticlause = [0]*len(self.important_variables)
                    v0 = min(list(self.important_variables))
                    i = 0
                    sollist = sol.split()
                    for s in sollist:
                        try:
                            w = int(s)
                        except ValueError:
                            continue
                        if abs(w) in self.important_variables:
                            anticlause[i] = -w
                            i += 1
                    anticlause = ' '.join([str(a) for a in anticlause if (a != 0)])
                    cnf_fifo.write('%s 0\n' % anticlause)
                    npreds += 1
                    if firstsol is None:
                        firstsol = sol
                    if findany:
                        return npreds, firstsol
                    #outqueue.put(sol)
                    pop = self.getpop(sol, 1)
                    if pop < minpop:
                        minpop = pop
                        minsol = sol
                elif sol[:5] == 'INDET':
                    running = False
                else:
                    print("UNSAT")
                    stages_completed = 2
                    break

        finally:

            if running:
                # Kill iglucose by writing rubbish into the pipe:
                cnf_fifo.write('error\n')
                cnf_fifo.flush()
                stages_completed = 2

            # Close and delete the FIFOs:
            cnf_fifo.close()
            sol_fifo.close()
            os.unlink(sol_fifoname)
            os.unlink(cnf_fifoname)

        return npreds, minsol


def readsol(solstr, yoff = 0, xoff = 0):
    rows = solstr.split("\n")
    result = {}
    states = {".": DEAD_VARIABLE_STATE, "*": LIVE_VARIABLE_STATE}
    maxx = 0
    maxy = 0
    x = xoff
    for r in rows:
        r = r.replace('\n', '').replace(' ','')
        if len(r) == 0:
            continue
        y = yoff
        for c in r:
            if c not in states:
                continue
            result[(x, y)] = states[c]
            y += 1
        x += 1
        maxx = max(x, maxx)
        maxy = max(y, maxy)
    print(maxx, maxy)
    return result, maxx - xoff, maxy - yoff


def inbox(bbox, coords):
    if bbox[0] > coords[0] or bbox[1] < coords[0]:
        return False
    if bbox[2] > coords[1] or bbox[3] < coords[1]:
        return False
    return True


def updatelimits(bbox, coords):
    bbox[0] = min(bbox[0], coords[0])
    bbox[1] = max(bbox[1], coords[0])
    bbox[2] = min(bbox[2], coords[1])
    bbox[3] = max(bbox[3], coords[1])
    return bbox


def spiralcoords():
    limits = np.zeros(4)  # minx, maxx, miny, maxy
    coords = np.zeros(2)  # x, y
    directions = [(1, 0), (0, -1), (-1, 0), (0, 1)]
    directions = [np.array(x) for x in directions]
    dir_index = 0
    direction = directions[dir_index]
    while True:
        yield coords
        coords += direction
        if not inbox(limits, coords):
            limits = updatelimits(limits, coords)
            dir_index = (dir_index + 1) % len(directions)
            direction = directions[dir_index]

def getbbox(coords):
    bbox = np.zeros(4)
    for c in coords:
        bbox = updatelimits(bbox, c)
    return bbox


def getpositivecoords(n):
    spiral = spiralcoords()
    coordsarr = [spiral.next().copy() for i in range(n)]
    bbox = getbbox(coordsarr)
    mins = np.array([bbox[0], bbox[2]], dtype="int32")
    maxs = np.array([bbox[1], bbox[3]], dtype="int32")
    maxs -= mins
    coordsarr = [x - mins for x in coordsarr]
    return coordsarr, maxs

def getcells(values, pad):
    n = len(values)
    coordsarr, maxs = getpositivecoords(n)
    result = {}
    for i in range(n):
        state = DEAD_VARIABLE_STATE
        if values[i]:
            state = LIVE_VARIABLE_STATE
        coords = tuple(coordsarr[i] + np.array([pad, pad]))
        result[coords] = state
    return result, maxs[0] + 1, maxs[1] + 1


def search(valsarr, findany=False, pad=4, period=1):
    order = [[0], [1]]

    for v in order:
        valsarr += v
        setcells, x, y = getcells(valsarr, pad)
        a = PredecessorSearch(period + 1, x + 2 * pad, y + 2 * pad, pad, setcells, oscillator=True, allunknown=False,
                              forcerim=False, forcephoenix=False)
        npreds, pred = a.exhaust("test%d" % os.getpid(), "test%d" % os.getpid(), timeout=10000000, findany=findany)
        print("some" if npreds else "no", "extensions")
        if pred is not None:
            a.printsol(pred)
        if npreds == 0:
            for i in v:
                valsarr.pop()
            continue
        print(valsarr)
        print("advancing to step", len(valsarr) + len(v), "with", v)
        search(valsarr,  pad=pad, period=period)
        for i in v:
            valsarr.pop()
    print("backtracking to step", len(valsarr))
    return 0





if __name__ == "__main__":
    starttime = time.time()
    valsarr = [1, 1, 1, 1, 1, 1, 1, 1, 1]
    search(valsarr, pad=5, period=2)
    # TODO: instead of using raw "number of predecessors," use "minimum difference between first and last":
    # number of cells (in important_variables) that take on multiple values across the predecessors
    # at least, I think that's what they meant
    # Or maximum edit distance between predecessors?
    # todo: anticlause generation is a massive bottleneck, needs to be in a different language
    # ammendum to the above: it's only about half the time after turning off the debugger. Still probably worth porting
    endtime = time.time()
    print("finished in %2.2f seconds" % (endtime - starttime))

