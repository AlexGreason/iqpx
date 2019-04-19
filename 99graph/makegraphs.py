import numpy as np
import networkx as nx
from sys import stdout, stderr
from tqdm import tqdm

def getadj(a, b, *cees):
    
    things = []
    i = 4
    things.append([0] + [j for j in xrange(i, i+a)] + [1])
    i += a
    things.append([2] + [j for j in xrange(i, i+b)] + [3])
    i += b
    for c in cees:
        things.append([j for j in xrange(i, i+c)] + [i])
        i += c
    things = [zip(x[1:], x[:-1]) for x in things]
    return [a[::i] for b in things for a in b for i in [-1, 1]]

def cycle_types(n, k=3):
    if (n == 0):
        yield []
    for i in xrange(k, n+1):
        for m in cycle_types(n-i, i):
            yield [i] + m
            
def forty_two(n):
    for i in xrange(n+1):
        for j in xrange(i//2+1):
            for m in cycle_types(n-i):
                yield [i-j, j] + m
                
def involutions(labels):
    if len(labels) == 0:
        yield []
    else:
        a = labels[0]
        for b in labels[1:]:
            ll = [x for x in labels if x not in [a, b]]
            for i in involutions(ll):
                yield i + [(a, b), (b, a)]

def blue_adjacencies(d):
    for x in forty_two(d-4):
        e = np.array(getadj(*x))
        z = np.zeros((d, d))
        np.add.at(z, tuple(e.T), 1)
        yield z

def red_adjacencies(d):
    
    things = [(0,1,2,3), (0,1,3,2), (0,2,1,3), (0,2,3,1), (0,3,1,2), (0,3,2,1),
              (1,2,0,3), (1,0,2,3), (1,3,0,2), (1,0,3,2), (2,0,1,3), (2,1,0,3)]
    things = [zip(x[1:], x[:-1]) for x in things]
    
    for i in involutions(list(range(4, d))):
        for j in things:
            e = np.array([t[::l] for t in j for l in [-1, 1]] + i)
            z = np.zeros((d, d))
            np.add.at(z, tuple(e.T), 1)
            yield z

def all_graphs(d):
    
    header = True
    ra = list(red_adjacencies(d))
    ba = list(blue_adjacencies(d))
    canvas = np.zeros((2*d+1, 2*d+1))
    canvas[d:2*d][:,0:d] += np.identity(d)
    canvas[d:2*d][:,2*d] += 1
    canvas += canvas.T

    stderr.write('%d possibilities\n' % (len(ra) * len(ba)))

    for r in tqdm(ra):
        for b in ba:
            if np.sum(r * b) < 0.5:
                canvas[0:d][:,0:d] = r
                canvas[d:2*d][:,d:2*d] = b
                yield nx.to_graph6_bytes(nx.from_numpy_matrix(np.array(canvas, dtype=int)), header=header)
                header = False

if __name__ == '__main__':

    for s in all_graphs(14):
        stdout.write(s)
