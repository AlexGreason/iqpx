import itertools
import networkx as nx
import numpy as np
from tqdm import tqdm
from math import factorial

from grills import *

def multinomial_coefficient(*args):

    for x in args:
        if (x < 0):
            return 0

    p = factorial(sum(args))
    for x in args:
        p /= factorial(x)

    return int(p)

def binomial_coefficient(n, r):

    return multinomial_coefficient(n - r, r)

def get_cases():

    return nx.read_graph6('99graph/isofree.g6')

def get_vertices():

    verts = [(sum(map(abs, x)), x) for x in itertools.product([-1, 0, 1], repeat=7)]
    verts = sorted(verts)[:99]
    return np.array([x[1] for x in verts], dtype=int)

def interpret_case(G, verts=get_vertices()):

    centres = [i for i in xrange(len(G)) if G.degree[i] == 14]

    if (len(centres) != 1):
        raise ValueError('G must have a single degree-14 vertex.')

    centre = centres[0]

    paths = nx.shortest_path(G, source=centre)

    outers = {x : y[1] for (x, y) in paths.iteritems() if (len(y) == 3)}

    H = G.subgraph(list(outers)).copy()
    hd = dict(H.degree)

    if (sorted(hd.values()) != ([1]*12 + [2]*2)):
        raise ValueError('Non-neighbours of the root must induce a subgraph with 12 degree-1 and 2 degree-2 vertices.')

    mo = [i for (i, j) in hd.items() if j == 2]
    H.remove_edge(*mo)
    bij = {k : v for (k, v) in [t[::p] for t in H.edges for p in [-1, 1]]}
    outerseq = mo + [i for (i, j) in H.edges if ((i not in mo) and (j not in mo))]
    outerseq += [bij[i] for i in outerseq[::-1]]

    middleseq = [outers[i] for i in outerseq]
    H = G.subgraph(middleseq)
    if ([H.degree[i] for i in middleseq] != ([1]*2 + [2]*10 + [1]*2)):
        raise ValueError('Neighbours of the root induce an incorrect subgraph.')

    vdict = {tuple(j) : i for (i, j) in enumerate(verts)}
    middleseq = {v : verts[i+1] for (i, v) in enumerate(middleseq)}

    outer2s = [y[3] for y in paths.values() if (len(y) == 4)]
    outer2s = {k : tuple([y for (x, y) in outers.iteritems() if x in G[k]]) for k in outer2s}
    outer2s = {k : vdict[tuple(middleseq[i] + middleseq[j])] for (k, (i, j)) in outer2s.iteritems()}

    # Compute the remaining neighbours of vertex 15.
    n15 = [vdict[tuple(middleseq[i] + middleseq[j])] for (i, j) in H.edges()]

    xedges = [(outer2s[i], outer2s[j]) for (i, j) in G.subgraph(list(outer2s)).edges()]

    return (set(n15), set(xedges))


def graph_edges(G, verts=get_vertices()):

    edges = {}
    for i in xrange(15):
        for j in xrange(i+1, 99):
            edges[(i, j)] = (np.square(verts[i] - verts[j]).sum() == 1)

    for i in xrange(1, 8):
        edges[(i, 15-i)] = True

    n15, xedges = interpret_case(G, verts)
    for j in xrange(16, 99):
        edges[(15, j)] = (j in n15)

    if (len(xedges) == 0):
        return edges

    for i in n15:
        for j in n15:
            if (i < j):
                if ((i, j) in xedges) or ((j, i) in xedges):
                    edges[(i, j)] = True
                else:
                    edges[(i, j)] = False

    return edges


def binarise_graph(*args, **kwargs):

    edges = graph_edges(*args, **kwargs)
    return ''.join([('1' if edges[(i, j)] else '0') for i in xrange(16) for j in xrange(i+1, 99)])


def flatten(x):

    if hasattr(x, '__iter__'):
        for i in x:
            for j in flatten(i):
                yield j
    else:
        yield x


class grapheme(satinstance):

    def hasedge(self, i, j):
        if (i == j):
            return False
        t = (min(i, j), max(i, j))
        if t not in self.edges:
            return self.ev[t]
        return bool(self.edges[t])

    def assert_at_least(self, variables, tot):
        if (tot == 0):
            pass
        elif (tot == 1):
            self.newclause(*variables)
        elif (tot == 2):
            for v in variables:
                self.newclause(*[w for w in variables if (w != v)])
        else:
            raise ValueError('tot should be 0, 1, or 2.')

    def assert_less_than(self, variables, tot, using=None):

        if using is None:

            # Trivial constraints:
            if (len(variables) == tot):
                self.newclause(*[-x for x in variables])
            if (len(variables) <= tot):
                return

            # Determine heuristically whether to use ancilla variables or
            # not. In general, avoid doing so unless we have at least a
            # twofold saving on the number of clauses.
            using = []
            if (tot >= 3):
                ancillae_cost  = binomial_coefficient(len(variables) + 1, 2)
                ancillae_cost *= binomial_coefficient(tot, 2)
                ordinary_cost  = binomial_coefficient(len(variables), tot)
                if (ancillae_cost * 2 < ordinary_cost):
                    using = 'ancillae'

        if isinstance(using, basestring) and (using == 'ancillae'):
            newvars = []
            for v in variables:
                newvars.append([self.newvar() for _ in xrange(tot - 1)])
                cl = [-x for x in flatten(v)] + newvars[-1]
                self.newclause(*cl)

            for i in xrange(len(newvars)):
                for j in xrange(i, len(newvars)):
                    for k in xrange(tot-1):
                        for l in xrange(k, tot-1):
                            if (i < j) or (k < l):
                                # Force true variables to form an antichain in
                                # the interests of symmetry breaking:
                                self.newclause(-newvars[i][k], -newvars[j][l])

            # Subject to the antichain condition, we can force a few variables
            # to be false without loss of generality:
            for i in xrange(tot-2):
                for j in xrange(tot-2-i):
                    self.newclause(-newvars[i][j])
                    self.newclause(-newvars[-(1+i)][-(1+j)])

        elif (len(using) == tot):
            self.newclause(*[-x for x in flatten(using)])
        else:
            for (i, v) in enumerate(variables):
                self.assert_less_than(variables[i+1:], tot, using + [v])

    def __init__(self, G):

        super(grapheme, self).__init__()

        # Obtain a dictionary of known edges and non-edges:
        if isinstance(G, dict):
            self.edges = G
        elif isinstance(G, nx.Graph):
            self.edges = graph_edges(G)
        else:
            raise TypeError("G must be either a nx.Graph or dict.")

        # Construct variables for each vertex-pair:
        self.ev = {}
        for i in xrange(98):
            for j in xrange(i+1, 99):
                if (i, j) not in self.edges:
                    self.ev[(i, j)] = self.apply_state_to_variable(UNKNOWN_VARIABLE_STATE)
                else:
                    c = (LIVE_VARIABLE_STATE if self.edges[(i, j)] else DEAD_VARIABLE_STATE)
                    self.apply_state_to_variable(c)

        reme = [(i, j) for i in xrange(1, 98) for j in xrange(max(15, i+1), 99)]

        for (i, j) in tqdm(reme):
            ij = []
            cn = 0
            for k in xrange(99):
                ki = self.hasedge(i, k)
                kj = self.hasedge(j, k)
                if ki and kj:
                    t = [a for a in (ki, kj) if not isinstance(a, bool)]
                    if len(t) == 0:
                        cn += 1
                    else:
                        ij.append(t)

            te = self.hasedge(i, j)

            if isinstance(te, bool):
                # Known edge or non-edge:
                cn += (1 if te else 0)
                self.assert_less_than(ij, 3 - cn)
                if (i < 15):
                    self.assert_at_least([l for (l,) in ij], 2 - cn)
            else:
                self.assert_less_than(ij + [te], 3 - cn)

if __name__ == '__main__':

    cases = get_cases()
    for G in tqdm(cases):
        print binarise_graph(G)

