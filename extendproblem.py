from grills import *
from iqpx import calculate_padding, canon6
from parserle import rle2bin
from velocities import parse_velocity, partial_derivatives
from sys import stdout
from collections import Counter
import multiprocessing
import random
import argparse
import signal
import cPickle
import gzip
import time
import math as m


class PartialExtender(basegrill):

    def __init__(self, W, K, initial_rows, params):

        super(PartialExtender, self).__init__()
        '''
        This constructor converts the problem (a rectangular grid of
        coordinates in logical (u,v)-space) into a set of (t, x, y) triples
        in physical spacetime, which are then fed to the basegrill. That is
        to say, this abstracts away the lattice quotient so that we can
        re-use the same code from GRILLS.
        '''

        # Safe amount of horizontal padding:
        HPADDING = calculate_padding(params['dudt'], params['dudx'], params['dudy'])

        initialcanon, initialwidth = canon6(initial_rows)
        full_width = W + 2 * HPADDING
        true_width = max(full_width, initialwidth + 2 * HPADDING)

        self.full_width = true_width
        halfwidth = lambda x: int(m.ceil(float(x)/2) - 1)
        initialpad = halfwidth(true_width) - halfwidth(initialwidth)
        fullpad = halfwidth(true_width) - halfwidth(W)
        self.full_height = len(initial_rows) + 1 + K
        self.important_variables = set([])
        self.bottom_variables = set([])
        self.bottom_edge_variables = set([])
        self.initial_rows = initial_rows

        p = params['p']
        a = params['a']
        dvdy = params['dvdy']
        dudy = params['dudy']
        dvdt = params['dvdt']

        self.reverse = params['reverse'] if ('reverse' in params) else False
        for v in xrange(self.full_height):
            for u in xrange(self.full_width):
                if v < len(initial_rows):
                    if u < initialpad:
                        state = DEAD_VARIABLE_STATE
                    else:
                        state = 1 << ((initial_rows[v] >> (u - initialpad)) & 1)
                elif (u < fullpad) or (u >= self.full_width - fullpad):  # second condition shouldn't trigger
                    state = DEAD_VARIABLE_STATE
                else:
                    state = UNKNOWN_VARIABLE_STATE

                variable = self.apply_state_to_variable(state)

                for t in xrange(p + 1):
                    ev = (-v) if self.reverse else v
                    xp = dvdy * u - dudy * ev - a * t
                    yq = ev - t * dvdt
                    if xp % p != 0:
                        continue
                    if yq % dvdy != 0:
                        continue
                    x = xp // p
                    y = yq // dvdy
                    self.relate(variable, (t, x, y))

                if (state == UNKNOWN_VARIABLE_STATE) and (v >= len(initial_rows)) and (v < len(initial_rows) + p):
                    self.important_variables.add(variable)
                if v >= (self.full_height - len(initial_rows)):
                    self.bottom_variables.add(variable)
                    if (u < fullpad + 1) or (u >= self.full_width - fullpad - 1):
                        self.bottom_edge_variables.add(variable)
                #if v >= (self.full_height - 2 * len(initial_rows)):
                #    if (u < fullpad + 1) or (u >= self.full_width - fullpad - 1):
                #        self.bottom_edge_variables.add(variable)
        self.enforce_symmetry()

    def enforce_symmetry(self):
        for (gen, x, y) in self.cells:
            self.identify(self.cells[(gen, x, y)], self.cells[(gen, self.full_width - x - 1, y)])

    def sol2rows(self, sol):
        """
        Converts an iglucose solution string into a tuple of rows represented
        as unsigned integers.
        """
        positives = {}
        for s in sol.split():
            try:
                w = int(s)
                positives[abs(w)] = (1 if (w > 0) else 0)
            except ValueError:
                continue
        rows = [sum([positives[(x * self.full_width) + i + 1] << i for i in xrange(self.full_width)]) for x in
                xrange(self.full_height)]
        return tuple(rows)

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

        try:
            cnf_fifo.write('p inccnf\n')
            self.write_dimacs(cnf_fifo, write_header=False)

            # Look for complete solutions:
            if skip_complete:
                stages_completed = 1
            else:
                stages_completed = 0
                cnf_fifo.write('a %s 0\n' % (' '.join([str(-x) for x in self.bottom_variables])))
                cnf_fifo.flush()
                sol = sol_fifo.readline()

                if sol[:3] == 'SAT':
                    # Completion found:
                    print("found completion of ", self.initial_rows, "with", self.sol2rows(sol))
                    outqueue.put((name, self.sol2rows(sol)))
                    satisfied = True
                elif sol[:5] == 'INDET':
                    running = False

            #cnf_fifo.write('a %s 0\n' % (' '.join([str(-x) for x in self.bottom_edge_variables])))
            #cnf_fifo.flush()


            # Try to extend the partial:
            while running:
                #cnf_fifo.write('a 0\n')
                cnf_fifo.write('a %s 0\n' % (' '.join([str(-x) for x in self.bottom_edge_variables])))
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
                    outqueue.put((name, self.sol2rows(sol)))
                elif sol[:5] == 'INDET':
                    running = False
                else:
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