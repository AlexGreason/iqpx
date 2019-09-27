import multiprocessing
import random
import argparse
import signal
import cPickle
import gzip
import time
import sys
import math

from grills import *
from parserle import rle2bin
from velocities import parse_velocity, partial_derivatives
from sys import stdout
from collections import Counter

import subprocess

import numpy as np


class OscillatorSearch(basegrill):

    def __init__(self, g, m, n, padding, forceedge=False, forcerim=False, forcephoenix=False, periodic=False, forcefull=False, forcecenter=False, forcecenterchange=False):
        super(OscillatorSearch, self).__init__()
        print("g", g, "m", m, "n", n, "padding", padding, "forcerim", forcerim, "forcephoenix", forcephoenix, "periodic", periodic, "forcefull", forcefull, "forcecenter", forcecenter)
        self.g = g
        self.m = m
        self.n = n
        self.padding = padding
        self.important_variables = set()

        for t in range(g):
            for x in range(m):
                for y in range(n):
                    state = UNKNOWN_VARIABLE_STATE
                    if forcerim:
                        if x < padding or abs(x - m + 1) < padding:
                            state = DEAD_VARIABLE_STATE
                        if y < padding or abs(y - n + 1) < padding:
                            state = DEAD_VARIABLE_STATE
                    if forceedge:
                        if x < 2 or y < 2:
                            state = DEAD_VARIABLE_STATE
                    if x == m//2 and y == n//2 and t == 0 and forcecenter:
                        state = LIVE_VARIABLE_STATE
                    if x == m//2 and  y == n//2 and t == 2 and forcecenterchange:
                        state = DEAD_VARIABLE_STATE

                    variable = self.apply_state_to_variable(state)
                    self.relate(variable, (t, x, y))
                    if t == 0 and x > padding and abs(x - self.m + 1) > padding and y > padding and abs(y - self.n + 1) > padding:
                        self.important_variables.add(variable)
                    else:
                       if forcephoenix and t > 0 and state == UNKNOWN_VARIABLE_STATE:
                           self.implies(self.cells[(t - 1, x, y)], -variable)
                    if t == g - 1:
                        self.relate(variable, (0, x, y))
            for x in range(m):
                for y in range(n):
                    if periodic:
                        if x < padding:
                            self.identify(self.cells[(t, x, y)], self.cells[(t, x + m - padding, y)])
                        if y < padding:
                            self.identify(self.cells[(t, x, y)], self.cells[(t, x, y + m - padding)])
        for t in range(g):
            if (forcefull and t != 0 and (g - 1) % t == 0 and t != (g - 1) and t != 1) or (t == 1 and not forcephoenix):
                print(t, 0, "forced different")
                self.forcedifferent(t, 0)
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


    def printsol(self, sol):
        print(sol)
        variables = {}
        for s in sol.split():
            try:
                w = int(s)
                variables[abs(w)] = (1 if (w > 0) else 0)
            except ValueError:
                continue
        print(variables)
        for x in range(self.m):
            for y in range(self.n):
                char = "."
                if variables[self.m * x + y + 1] == 1:
                    char = "*"
                sys.stdout.write(char)
            sys.stdout.write("\n")
        sys.stdout.write("\n")




    def exhaust(self, name, prefix, outqueue, timeout=600, skip_complete=False):
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
                    self.printsol(sol)
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

        return stages_completed, satisfied


if __name__ == "__main__":
    starttime = time.time()
    a = OscillatorSearch(5, 25, 25, 2, forceedge=True, forcerim=False, forcephoenix=True, forcefull=False,
                         forcecenter=True, periodic=False, forcecenterchange=True)
    a.exhaust("test", "test", multiprocessing.Queue(), timeout=10000000)
    endtime = time.time()
    print("finished in %2.2f seconds" % (endtime - starttime))

