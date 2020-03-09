from copy import copy

from iqpx import *


class AssumptionSearch(basegrill):
    def __init__(self, W, H, params):
        super(AssumptionSearch, self).__init__()
        self.HPADDING = calculate_padding(params['dudt'], params['dudx'], params['dudy'])
        self.params = params
        self.full_width = W + 2 * self.HPADDING
        self.full_height = H
        self.rows = {}

        p = params['p']
        a = params['a']
        dvdy = params['dvdy']
        dudy = params['dudy']
        dvdt = params['dvdt']

        for v in xrange(self.full_height):
            self.rows[v] = []
            for u in xrange(self.full_width):
                if (u < self.HPADDING) or (u >= self.full_width - self.HPADDING):
                    state = DEAD_VARIABLE_STATE
                else:
                    state = UNKNOWN_VARIABLE_STATE

                variable = self.apply_state_to_variable(state)

                for t in xrange(p + 1):
                    xp = dvdy * u - dudy * v - a * t
                    yq = v - t * dvdt
                    if xp % p != 0:
                        continue
                    if yq % dvdy != 0:
                        continue
                    x = xp // p
                    y = yq // dvdy
                    self.relate(variable, (t, x, y))
                    print((t, x, y))
                if state == UNKNOWN_VARIABLE_STATE:
                    self.rows[v].append(variable)
        self.enforce_symmetry()
        self.enforce_rule(preprocess=True)

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

    def sol2string(self, sol):
        positives = {}
        for s in sol.split():
            try:
                w = int(s)
                positives[abs(w)] = (1 if (w > 0) else 0)
            except ValueError:
                continue
        for y in xrange(self.full_height // self.params["p"]):
            for t in xrange(self.params["p"]):
                line = ""
                for x in xrange(self.HPADDING, self.full_width):
                    var = self.cells[(t, x, y)]
                    if positives[var]:
                        line += "*"
                    else:
                        line += "."
                print(line)
        print ""

    def sol2pat(self, sol):
        positives = {}
        for s in sol.split():
            try:
                w = int(s)
                positives[abs(w)] = (1 if (w > 0) else 0)
            except ValueError:
                continue
        for y in xrange(self.full_height // self.params["p"]):
                line = ""
                for x in xrange(self.HPADDING, self.full_width):
                    var = self.cells[(0, x, y)]
                    if positives[var]:
                        line += "*"
                    else:
                        line += "."
                print(line)
        print ""


    def rows2assump(self, initial_rows):
        p = self.params['p']
        a = self.params['a']
        dvdy = self.params['dvdy']
        dudy = self.params['dudy']
        dvdt = self.params['dvdt']

        result = []
        checked = set()

        for v in xrange(self.full_height):
            for u in xrange(self.full_width):
                if (u < self.HPADDING) or (u >= self.full_width - self.HPADDING):  # second condition shouldn't trigger
                    continue
                elif v < len(initial_rows):
                    state = 1 << ((initial_rows[v] >> (u)) & 1)
                else:
                    continue

                for t in xrange(p + 1):
                    xp = dvdy * u - dudy * v - a * t
                    yq = v - t * dvdt
                    if xp % p != 0:
                        continue
                    if yq % dvdy != 0:
                        continue
                    x = xp // p
                    y = yq // dvdy
                    variable = self.cells[(t, x, y)]
                    if variable not in checked:
                        if state == DEAD_VARIABLE_STATE:
                            result.append(-variable)
                        if state == LIVE_VARIABLE_STATE:
                            result.append(variable)
                        checked.add(variable)
        return result

    def setup(self, prefix, timeout):
        sol_fifoname = prefix + '.sol'
        cnf_fifoname = prefix + '.icnf'

        if os.path.exists(sol_fifoname):
            os.unlink(sol_fifoname)
        if os.path.exists(cnf_fifoname):
            os.unlink(cnf_fifoname)

        os.mkfifo(sol_fifoname)
        os.mkfifo(cnf_fifoname)

        cnf_fifo = open(cnf_fifoname, 'w+')
        run_iglucose(("-cpu-lim=%d" % int(timeout)), cnf_fifoname, sol_fifoname)
        sol_fifo = open(sol_fifoname, 'r')

        cnf_fifo.write('p inccnf\n')
        self.write_dimacs(cnf_fifo, write_header=False)
        return (cnf_fifo, sol_fifo)

    def ispossible(self, cnf_fifo, sol_fifo, assumption):
        assumpstr = 'a %s 0\n' % (' '.join([str(x) for x in assumption]))
        cnf_fifo.write(assumpstr)
        cnf_fifo.flush()
        sol = sol_fifo.readline()

        if sol[:3] == 'SAT':
            return sol
        else:
            return False

    def search(self, cnf_fifo, sol_fifo, toassign, assigned, solutions, state, order):
        print(assigned)
        if len(toassign) == 0:
            solutions.append(copy(assigned))
            # sol = self.ispossible(cnf_fifo, sol_fifo, state + assigned)
            # self.sol2pat(sol)
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
            self.search(cnf_fifo, sol_fifo, toassign[1:], assigned + [val], solutions, state, nextorder)

    def exhaust(self, cnf_fifo, sol_fifo, state, important_variables):
        solutions = []
        baseassumptions = self.rows2assump(state)
        self.search(cnf_fifo, sol_fifo, important_variables, [], solutions, baseassumptions, [1, -1])
        return solutions


if __name__ == "__main__":
    a, b, p = parse_velocity("5c/11o")
    params = partial_derivatives(a, b, p)
    search = AssumptionSearch(16, 2*p + 90, params)
    initialrows = tuple([0]*(2*p))
    assump = search.rows2assump(initialrows)
    important = search.rows[len(initialrows)]
    print(assump)
    cnf_fifo, sol_fifo = search.setup("atest", 10000000)
    start = time.time()
    sols = search.exhaust(cnf_fifo, sol_fifo, initialrows, important)
    print "finished in " + str(time.time() - start)
    print(sols)
    print(len(sols))
    # for s in sols:
    #     print(search.sol2row(s, len(initialrows)))



