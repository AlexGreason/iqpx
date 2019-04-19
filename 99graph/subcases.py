import networkx as nx
import numpy as np
from tqdm import tqdm
from sys import stdout

def get_cases():

    return nx.read_graph6('isofree.g6')

def involutions(labels, forbidden=set([])):
    if len(labels) == 0:
        yield []
    else:
        a = labels[0]
        for b in labels[1:]:
            if ((a, b) in forbidden) or ((b, a) in forbidden):
                continue
            ll = [x for x in labels if x not in [a, b]]
            for i in involutions(ll, forbidden):
                yield i + [(a, b), (b, a)]

def subdivide_case(G):

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

    middle12 = {v : k for (k, v) in outers.iteritems() if k not in mo}

    new10 = [(middle12[x], middle12[y]) for (x, y) in G.subgraph(list(middle12)).edges()]
    new10 = {(i + len(G)) : j for (i, j) in enumerate(new10)}

    G.add_nodes_from(list(new10))
    G.add_edges_from([(x, z) for (x, y) in new10.iteritems() for z in y])

    forbidden = [(k, l) for (k, v) in new10.iteritems() for (l, w) in new10.iteritems() if (len(set(v + w)) != 4)]
    forbidden = set([t for t in forbidden if (t[0] < t[1])])

    invols = list(involutions(list(new10), forbidden))

    return (G, invols)

if __name__ == '__main__':

    header = True
    for c in tqdm(get_cases()):
        G, invols = subdivide_case(c)
        for iv in invols:
            H = G.copy()
            H.add_edges_from(iv)
            stdout.write(nx.to_graph6_bytes(H, header=header))
            header = False
