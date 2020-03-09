from assumptiononly import AssumptionSearch
import time
from iqpx import parse_velocity, partial_derivatives, printint
from copy import copy
import resource
import sys
resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
sys.setrecursionlimit(10000000)

class CandleSearch(AssumptionSearch):
    def __init__(self, W, H, params):
        super(CandleSearch, self).__init__(W, H, params)

    def shiftup(self, state):
        res = []
        for s in state:
            sign = s//abs(s)
            t = s - self.full_width
            if t > 0:
                res.append(t * sign)
        return res

    def completeassump(self):
        rows = []
        for i in range(self.params["p"] * 2):
            rows += self.rows[self.full_height - i - 1]
        result = []
        for r in rows:
            result.append(-r)
        return result

    def searchdfs(self, cnf_fifo, sol_fifo, toassign, assigned, state, order, row, partial, start=False):
        print(assigned)
        if len(toassign) == 0:
            if start:
                anylive = False
                for a in assigned:
                    if a > 0:
                        anylive = True
                if not anylive:
                    return
            #solutions.append(copy(assigned))
            # completion = self.completeassump()
            # sol = self.ispossible(cnf_fifo, sol_fifo, state + assigned + completion)
            # die = False
            # if sol:
            #     print("Complete ship")
            #     die = True
            # else:
            sol = self.ispossible(cnf_fifo, sol_fifo, state + assigned)
            rows = tuple(list(self.sol2rows(sol))[1:(2*self.params["p"])+1])
            sofar = partial + list(self.sol2rows(sol))[len(rows):]
            print(sofar)
            for i in range(0, len(sofar), self.params["p"]):
                printint(sofar[i])
            #self.sol2pat(sol)
            print(self.sol2rows(sol))
            print(rows)
            if list(rows) == [0]*len(rows):
                 return list(self.sol2rows(sol))
            print(partial + [list(rows)[-1]])
            newstate = self.rows2assump(rows)
            print(newstate)
            nextrow = self.rows[len(rows)]
            print "extending to row " + str(row + 1)
            res = self.searchdfs(cnf_fifo, sol_fifo, nextrow, [], newstate, [-1, 1], row + 1, partial + [list(rows)[-1]], start=False)
            if res:
                return [list(self.sol2rows(sol))[0]] + res
            return
        var = toassign[0]
        for o in order:
            val = o * var
            sol = self.ispossible(cnf_fifo, sol_fifo, state + assigned + [val])
            if not sol:
                print str(assigned + [val]) + " failed"
                continue
            positives = {}
            for s in sol.split():
                try:
                    w = int(s)
                    positives[abs(w)] = (1 if (w > 0) else 0)
                except ValueError:
                    continue
            if len(toassign) == 1 or positives[toassign[1]]:
                nextorder = [1, -1]
            else:
                nextorder = [-1, 1]
            res = self.searchdfs(cnf_fifo, sol_fifo, toassign[1:], assigned + [val], state, nextorder, row, partial, start=start)
            if res is not None:
                return res
        if len(assigned) == 0:
            print "Failed at row " + str(row) + ", backtracking"

    def exhaustdfs(self, cnf_fifo, sol_fifo, state):
        solutions = []
        row = len(state)
        important_variables = self.rows[row]
        baseassumptions = self.rows2assump(state)
        res = self.searchdfs(cnf_fifo, sol_fifo, important_variables, [], baseassumptions, [1, -1], row, list(state), start=True)
        if res is not None:
            for i in range(0, len(res), self.params["p"]):
                printint(res[i])
        return solutions

if __name__ == "__main__":
    # what if every time I backtracked back to a node, I increased the deepening at that node by one? (or K) (3 seems plausible)
    # Would require implementing the traceship-and-padding backed adaptive-deepening-with-one-sat-instance thing first
    # but it seems like increased lookahead decreases the branching factor at the cost of time-per-call
    # and the higher the branching factor the more that's worth.
    a, b, p = parse_velocity("3c/8o")
    params = partial_derivatives(a, b, p)
    search = CandleSearch(29, 2*p + 48, params)
    initialrows = tuple([0]*(2*p))
    assump = search.rows2assump(initialrows)
    important = search.rows[len(initialrows)]
    print(assump)
    cnf_fifo, sol_fifo = search.setup("atest", 10000000)
    start = time.time()
    sols = search.exhaustdfs(cnf_fifo, sol_fifo, initialrows)
    print "finished in " + str(time.time() - start)
    print(sols)
    print(len(sols))
    # for s in sols:
    #     print(search.sol2row(s, len(initialrows)))