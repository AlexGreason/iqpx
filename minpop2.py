from __future__ import print_function

from uniquefather import PredecessorSearch, getpositivecoords, readsol
import os
from grills import run_iglucose
from heapq import *
from minpop import rletoarr, arrtocelllist


class MinPredecessorSearch(PredecessorSearch):

    def __init__(self, m, n, padding, setcells, forcerim=True, stilllife=False, allunknown=False, rewindby=1):
        super(MinPredecessorSearch, self).__init__(m, n, padding, setcells, forcerim, stilllife, allunknown, rewindby)
        self.cnf_fifo = None
        self.sol_fifo = None

    def setup(self, prefix):
        sol_fifoname = prefix + '.sol'
        cnf_fifoname = prefix + '.icnf'

        if os.path.exists(sol_fifoname):
            os.unlink(sol_fifoname)
        if os.path.exists(cnf_fifoname):
            os.unlink(cnf_fifoname)

        os.mkfifo(sol_fifoname)
        os.mkfifo(cnf_fifoname)

        cnf_fifo = open(cnf_fifoname, 'w+')
        run_iglucose(("-cpu-lim=%d" % int(1000000000)), cnf_fifoname, sol_fifoname)
        sol_fifo = open(sol_fifoname, 'r')

        cnf_fifo.write('p inccnf\n')
        self.write_dimacs(cnf_fifo, write_header=False)
        self.cnf_fifo = cnf_fifo
        self.sol_fifo = sol_fifo

    def ispossible(self, assumption):
        assumpstr = 'a %s 0\n' % (' '.join([str(x) for x in assumption]))
        self.cnf_fifo.write(assumpstr)
        self.cnf_fifo.flush()
        sol = self.sol_fifo.readline()

        if sol[:3] == 'SAT':
            return sol
        else:
            return False

    def cellstoassump(self, cells, cellorder):
        result = []
        for i in range(len(cells)):
            if cells[i]:
                result.append(cellorder[i])
            else:
                result.append(-cellorder[i])
        return result

    def process(self, task, cellorder):
        pop, cells, order = task
        cellnum = len(cells)
        nextcell = cellorder[cellnum]
        base = self.cellstoassump(cells, cellorder)
        res = []
        for o in order:
            sol = self.ispossible(base + [o * nextcell])
            if not sol:
                continue
            positives = {}
            for s in sol.split():
                try:
                    w = int(s)
                    positives[abs(w)] = (1 if (w > 0) else 0)
                except ValueError:
                    continue
            if positives[nextcell]:
                nextorder = [1, -1]
            else:
                nextorder = [-1, 1]
            res.append([pop + positives[nextcell], cells + [positives[nextcell]], nextorder, sol])
        return res

    def getorder(self, gen=0):
        largedim = max(self.m, self.n)
        N = largedim**2
        coords = getpositivecoords(N)[0]
        result = []
        for c in coords:
            x, y = list(c)
            if (gen, x, y) in self.cells:
                result.append(self.cells[(gen, x, y)])
        return result

    def search(self):
        cellorder = self.getorder(gen=0)
        queue = [(0, [], [-1, 1])]
        heapify(queue)
        maxcells = 0
        minpop = 9999
        processed = 0
        while True:
            task = heappop(queue)
            pop, cells, order = task
            if len(cells) == len(cellorder):
                print("Finished")
                return
            sols = self.process(task, cellorder)
            processed += 1
            if processed % 200 == 0:
                print("processed " + str(processed) + ", queue length " + str(len(queue)))
            for s in sols:
                pop, cells, order, sol = s
                if len(cells) > maxcells or (len(cells) == maxcells and pop < minpop):
                    print((pop, cells, order))
                    print("Got population of " + str(pop) + " at cellnum " + str(len(cells)))
                    maxcells = len(cells)
                    minpop = pop
                    self.printsol(sol, gen=0)
                heappush(queue, (pop, cells, order))



if __name__ == "__main__":
    #code = "18bo$17b3o$12b3o4b2o$11bo2b3o2bob2o$10bo3bobo2bobo$10bo4bobobobob2o$12bo4bobo3b2o$4o5bobo4bo3bob3o$o3b2obob3ob2o9b2o$o5b2o5bo$bo2b2obo2bo2bob2o$7bobobobobobo5b4o$bo2b2obo2bo2bo2b2obob2o3bo$o5b2o3bobobo3b2o5bo$o3b2obob2o2bo2bo2bob2o2bo$4o5bobobobobobo$10b2obo2bo2bob2o2bo$13bo5b2o5bo$b2o9b2ob3obob2o3bo$2b3obo3bo4bobo5b4o$2b2o3bobo4bo$2b2obobobobo4bo$5bobo2bobo3bo$4b2obo2b3o2bo$6b2o4b3o$7b3o$8bo!"
    code = "2bo$bobo$obobo$obo2bo$bo2b2o$2b2o2b2o$4bo2bo$4b2o!"
    arr = rletoarr(code, 3, 3)
    print(arr)
    setcells = arrtocelllist(arr)
    print(setcells)
    search = MinPredecessorSearch(arr.shape[0], arr.shape[1], 2, setcells, rewindby=4)
    search.setup("test")
    search.search()