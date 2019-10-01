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

    def __init__(self, m, n, padding, setcells, forcerim=True, stilllife=False, allunknown=False):
        super(PredecessorSearch, self).__init__()
        print("m", m, "n", n, "padding", padding)
        self.g = 3 if stilllife else 2
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
                    if t == 1 and (x, y) in setcells:
                        state = setcells[(x, y)]
                    variable = self.apply_state_to_variable(state)
                    self.relate(variable, (t, x, y))
                    if t == 0 and ((x, y) in setcells) or (allunknown and state == UNKNOWN_VARIABLE_STATE):
                        self.important_variables.add(variable)
        if stilllife:
            for x in range(m):  # forces gen 1 to be a still life
                for y in range(n):
                    self.identify(self.cells[(1, x, y)], self.cells[(2, x, y)])
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
        self.newclause(*diffs)

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

    def exhaust(self, name, prefix, timeout=600, skip_complete=False):
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
        try:
            cnf_fifo.write('p inccnf\n')
            self.write_dimacs(cnf_fifo, write_header=False)

            # Try to extend the partial:
            while running:
                cnf_fifo.write('a 0\n')
                cnf_fifo.flush()
                sol = sol_fifo.readline()
                if sol[:3] == 'SAT':
                    satisfied = True
                    stages_completed = 1
                    anticlause = []
                    next_term = 0
                    v0 = min(list(self.important_variables))
                    for s in sol.split():
                        try:
                            w = int(s)
                        except ValueError:
                            continue
                        if abs(w) in self.important_variables:
                            anticlause.append(-w)
                            if w > 0:
                                next_term |= (1 << (w - v0))
                    anticlause = ' '.join([str(a) for a in anticlause if (a != 0)])
                    cnf_fifo.write('%s 0\n' % anticlause)
                    npreds += 1
                    #outqueue.put(sol)
                    #pop = self.getpop(sol, 1)
                    #if pop < minpop:
                    #    minpop = pop
                    #    print("population", pop)
                    #    self.printsol(sol)
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

        return npreds


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

if __name__ == "__main__":
    starttime = time.time()
    solstr = """
    ****
    ....
    ***
    """
    pad = 5
    yoff = pad
    xoff = pad
    setcells, x, y = readsol(solstr, yoff=yoff, xoff=xoff)
    a = PredecessorSearch(x + 2 * pad, y + 2 * pad, pad, setcells, stilllife=True, allunknown=False)
    #hang on, when I force the central cell to dead on gen 2, does that override the life rules?
    npreds = a.exhaust("test%d" % os.getpid(), "test%d" % os.getpid(), timeout=10000000)
    print(npreds, "predecessors")
    endtime = time.time()
    print("finished in %2.2f seconds" % (endtime - starttime))

