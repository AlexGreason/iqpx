# GRILLS -- Golly-Regulated Interactive Logic Life Search
from sys import stderr
import os
import subprocess
import shutil

# These should match the states in the rule table, and can be modified
# here to facilitate future expansion:
DEAD_VARIABLE_STATE = 1
LIVE_VARIABLE_STATE = 2
UNKNOWN_VARIABLE_STATE = 3
DISJUNCTIVE_VARIABLE_STATE = 4

ORIGIN_STATE = 6
VERTICAL_LINE_STATE = 7
ZEROTH_GENERATION_STATE = 8

try:
    import golly as g
    within_golly = True
    scriptdir = os.getcwd()
except ImportError as e:
    within_golly = False
    scriptdir = os.path.dirname(os.path.realpath(__file__))

cygwin_dir = None

def cygdir():
    # Find the Cygwin64 installation directory

    if (cygwin_dir is not None) and os.path.exists(cygwin_dir):
        return cygwin_dir
    elif os.path.exists('C:\\cygwin64'):
        return 'C:\\cygwin64'
    elif os.path.exists('C:\\cygwin'):
        return 'C:\\cygwin'

    if within_golly:
        dirname = g.opendialog("Please find the Cygwin64 install directory (e.g. C:\\cygwin64)", "dir")
    else:
        dirname = raw_input("Please type the Cygwin64 install directory (e.g. C:\\cygwin64): ")

    if os.path.exists(dirname):
        cygwin_dir = dirname
        return cygwin_dir
    else:
        raise ValueError("No Cygwin installation directory specified.")

def runbash(*args):
    # Run bash (in Cygwin if on Windows, or /bin/bash otherwise):

    if os.name == 'posix':
        # This works on Linux, Cygwin, and Mac:
        bash_file = '/bin/bash'
    elif os.name == 'nt':
        # We're in a non-Cygwin Windows environment:
        bash_file = os.path.join(cygdir(), 'bin', 'bash.exe')
    else:
        raise ValueError("os.name must be 'posix' for Linux/Cygwin/Mac or 'nt' for Windows")

    status = subprocess.call([bash_file] + list(args))
    return status

def run_iglucose(*args):
    '''
    Run an instance of iglucose in the background with specified arguments.
    We can communicate with it using named pipes (FIFOs).
    '''

    status = runbash(os.path.join(scriptdir, 'scripts', 'bgiglucose.sh'), *args)
    return status

def spliterable(it, predicate):
    pl = []
    for x in it:
        if predicate(x):
            yield pl
            pl = []
        else:
            pl.append(x)
    yield pl

def cartesian_product(*args):

    if len(args) == 0:
        return [tuple([])]
    else:
        ml = list(args[-1])
        return (x + (y,) for x in cartesian_product(*args[:-1]) for y in ml)

def get_life_transitions():

    trans = []

    for i in xrange(256):
        bits = bin(256 + i)[-8:]
        hw = bits.count('1')
        trans.append(('11' if (2 <= hw <= 3) else '10') + bits)
        trans.append(('01' if (hw == 3) else '00') + bits)

    return [int(t.replace('1', 'a').replace('0', '01').replace('a', '10'), 2) for t in trans]

LIFE_TRANSITIONS = get_life_transitions()
MEMOIZED_POSS2 = {}

def get_poss2(poss):
    if poss not in MEMOIZED_POSS2:
        reltrans = [z for z in LIFE_TRANSITIONS if ((z & poss) == z)]
        MEMOIZED_POSS2[poss] = reduce((lambda a, b : a | b), reltrans, 0)
    return MEMOIZED_POSS2[poss]


class satinstance(object):
    '''
    Base class for a SAT instance.
    '''

    def __init__(self):
        self.nvars = 0
        self.clauses = []
        self.known_states = {}

    def write_dimacs(self, f, write_header=True):
        if isinstance(f, basestring):
            # We've been given a filename instead of a file-handle:
            with open(f, 'w') as x:
                self.write_dimacs(x, write_header=write_header)
        else:
            # Write the DIMACS header and clauses:
            if write_header:
                f.write('p cnf %d %d\n' % (self.nvars, len(self.clauses)))
            for clause in self.clauses:
                f.write('%s 0\n' % clause)

    def write_and_simplify(self, dimacs_dir, dimacs_out=None, simptime=1800):

        if self.easy_unsat():
            return 'UNSAT'

        if os.path.exists(dimacs_dir):
            print('Directory %s already exists.' % dimacs_dir)
        else:
            os.makedirs(dimacs_dir)
            print('Directory %s created.' % dimacs_dir)

        if dimacs_out is None:
            dimacs_out = os.path.join(dimacs_dir, 'original.cnf')

        self.write_dimacs(dimacs_out)
        runbash(os.path.join(scriptdir, 'scripts', 'preprocess.sh'), dimacs_out, dimacs_dir, str(simptime + 15))
        with open(os.path.join(dimacs_dir, 'simp_status.txt'), 'r') as f:
            simp_status = ''.join(f.read().split())

        if simp_status[:5] == 'UNSAT':
            return 'UNSAT'

        if simp_status[:3] == 'SAT':
            return 'SAT'

        runbash(os.path.join(scriptdir, 'scripts', 'head_and_tail.sh'), dimacs_dir)
        return 'INDET'

    def newvar(self):
        self.nvars += 1
        return self.nvars

    def newclause(self, *args):
        # We convert to a string immediately to save memory:
        args = [str(a) for a in args if (a != 0)]
        self.clauses.append(' '.join(args))

    def implies(self, x, y):
        self.newclause(-x, y)

    def identify(self, *args):
        # Set two or more variables to be identical:
        for i in args:
            for j in args:
                if (i != j):
                    self.implies(i, j)

    def apply_state_to_variable(self, c, v=None):

        if v is None:
            v = self.newvar()
        if ((c & 2) == 0):
            self.newclause(-v)
        if ((c & 1) == 0):
            self.newclause(v)
        self.known_states[v] = c

        return v

    def easy_unsat(self):
        for c in self.known_states.itervalues():
            if (c == 0):
                return True
        return False


class basegrill(satinstance):
    '''
    This contains functionality for treating GoL situations as SAT problems.
    '''

    def __init__(self):
        super(basegrill, self).__init__()
        self.cache = {}
        self.cells = {}

    def relate(self, v, coords):
        if coords in self.cells:
            self.identify(v, self.cells[coords])
        else:
            self.cells[coords] = v

    def variadic_sum(self, *args, **kwargs):

        # Replace Boolean coding with one-hot coding:
        args = [([0, x] if isinstance(x, int) else x) for x in args]

        minimum = kwargs.pop('minimum', 1)
        maximum = kwargs.pop('maximum', None) or (sum(map(len, args)) - len(args))

        z = {}
        def atleast(k):
            if k not in z:
                z[k] = self.newvar()
            return z[k]

        for t in cartesian_product(*[list(enumerate(a)) for a in args]):
            eyes, vees = zip(*t)
            k1 = sum([i for i in eyes])
            k2 = sum([(i if (i != 0) else len(args[j])) for (j, i) in enumerate(eyes)])
            k2 -= (len(args) - 1)
            if (minimum <= k1 <= maximum):
                self.newclause(atleast(k1), *[-v for v in vees])
            if (minimum <= k2 <= maximum):
                self.newclause(-atleast(k2), *[v for v in vees])

        return [(z[i] if (i in z) else 0) for i in xrange(maximum + 1)]

    def getv2(self, gen, x, y):
        key = 'v2 %d %d %d' % (gen, x, y)
        if key not in self.cache:
            self.cache[key] = self.variadic_sum(self.cells[(gen, x, y)], self.cells[(gen, x, y+1)])
        return self.cache[key]

    def geth2(self, gen, x, y):
        key = 'h2 %d %d %d' % (gen, x, y)
        if key not in self.cache:
            self.cache[key] = self.variadic_sum(self.cells[(gen, x, y)], self.cells[(gen, x+1, y)])
        return self.cache[key]

    def geth4(self, gen, x, y):
        key = 'h4 %d %d %d' % (gen, x, y)
        if key not in self.cache:
            self.cache[key] = self.variadic_sum(self.geth2(gen, x, y), self.geth2(gen, x, y+2))
        return self.cache[key]

    def getx2(self, gen, x, y):
        key = 'x2 %d %d %d' % (gen, x, y)
        if key not in self.cache:
            self.cache[key] = self.variadic_sum(self.cells[(gen, x, y-1)], self.cells[(gen, x, y+1)])
        return self.cache[key]

    def getx3(self, gen, x, y):
        key = 'x3 %d %d %d' % (gen, x, y)
        if key not in self.cache:
            self.cache[key] = self.variadic_sum(self.cells[(gen, x, y)], self.getx2(gen, x, y))
        return self.cache[key]

    def resolve(self, gen, x, y, quaternary=True, encoding='split'):

        if (encoding == 'knuth'):
            xf = x ^ 1
            yf = y ^ 1
            xd = x & xf
            yd = y & yf
            xo = x + x - xf
            yo = y + y - yf
            h4 = self.geth4(gen, xd, y-1)
            v2 = self.getv2(gen, xo, yd)
            o2 = self.variadic_sum(self.cells[(gen, xf, y)], self.cells[(gen, xo, yo)])
            s = self.variadic_sum(h4, self.variadic_sum(v2, o2), minimum=2, maximum=4)
        elif (encoding == 'split'):
            x3_left = self.getx3(gen, x-1, y)
            x2_centre = self.getx2(gen, x, y)
            x3_right = self.getx3(gen, x+1, y)
            s = self.variadic_sum(x3_left, x2_centre, x3_right, minimum=2, maximum=4)
        elif (encoding == 'naive'):
            neighbours = [self.cells[(gen, x+i, y+j)] for i in [-1, 0, 1] for j in [-1, 0, 1] if ((i, j) != (0, 0))]
            s = self.variadic_sum(*neighbours, minimum=2, maximum=4)
        else:
            raise ValueError("'encoding' must be either 'knuth', 'split', or 'naive'")

        c = self.cells[(gen, x, y)]
        cc = self.cells[(gen+1, x, y)]
        self.newclause(-cc, -s[4])
        self.newclause(-cc, s[2])
        self.newclause(-cc, c, s[3])
        self.newclause(cc, s[4], -s[3])

        if quaternary:
            self.newclause(cc, -c, s[4], -s[2])
        else:
            yy = self.newvar()
            self.newclause(cc, -c, -yy)
            self.newclause(yy, s[4], -s[2])

    def enforce_rule(self, preprocess=True, **kwargs):
        '''
        Apply the transition constraints.
        '''

        modus_operandi = 'preprocess' if preprocess else 'resolve'

        total_optimisations = 0
        while (modus_operandi):
            optimisations = 0
            for (gen, x, y) in self.cells:
                poss = 0
                indets = 0
                dependents = [(gen, x, y), (gen+1, x, y), (gen, x-1, y), (gen, x+1, y), (gen, x, y-1),
                            (gen, x, y+1), (gen, x-1, y-1), (gen, x-1, y+1), (gen, x+1, y-1), (gen, x+1, y+1)]

                for t in dependents:
                    if t not in self.cells:
                        break
                    cv = self.known_states[self.cells[t]]
                    if (cv == UNKNOWN_VARIABLE_STATE):
                        indets += 1
                    poss = (poss << 2) | cv
                else:
                    if (modus_operandi == 'resolve'):
                        if (indets > 0):
                            self.resolve(gen, x, y, **kwargs)
                    if (modus_operandi == 'preprocess'):
                        # Possible compatible transitions:
                        poss2 = get_poss2(poss)
                        if (poss != poss2):
                            # We have made an inference:
                            for (i, t) in enumerate(dependents[::-1]):
                                oldcv = (poss  >> (2*i)) & 3
                                newcv = (poss2 >> (2*i)) & 3
                                if (oldcv != newcv):
                                    self.apply_state_to_variable(newcv, self.cells[t])
                                optimisations += 1
            total_optimisations += optimisations
            if (modus_operandi == 'preprocess'):
                if (optimisations == 0):
                    modus_operandi = 'resolve'
            elif (modus_operandi == 'resolve'):
                modus_operandi = None

    def load_solution(self, solution_file):
        if isinstance(solution_file, basestring):
            with open(solution_file, 'r') as f:
                self.load_solution(f)
        else:
            for l in solution_file:
                for x in l.split():
                    try:
                        v = int(x)
                        if (v > 0):
                            self.apply_state_to_variable(LIVE_VARIABLE_STATE, abs(v))
                        if (v < 0):
                            self.apply_state_to_variable(DEAD_VARIABLE_STATE, abs(v))
                    except:
                        pass


class grill(basegrill):
    '''
    This contains specific functionality for converting a GRILLS input
    pattern into a GoL scenario.
    '''

    def __init__(self):
        super(grill, self).__init__()
        self.gcells = {}

    def add_plane_gen(self, plane_gcells, gen, ox, oy):
        for (x, y, _) in plane_gcells:
            if (x, y) in self.gcells:
                v = self.gcells[(x, y)]
                self.relate(v, (gen, x-ox, y-oy))

    def add_plane(self, plane_gcells):
        origins = set([(x, y) for (x, y, c) in plane_gcells if (c == ORIGIN_STATE)])
        for (i, s) in enumerate(plane_gcells):
            (x, y, c) = s
            if (c >= ZEROTH_GENERATION_STATE):
                gen = c - ZEROTH_GENERATION_STATE
                ro = [(x+dx, y+dy) for dx in [-1, 0, 1] for dy in [-1, 0, 1]]
                ro = [origin for origin in ro if origin in origins]
                if (len(ro) != 1):
                    raise ValueError("(%d, %d, %d) has %d origins instead of one." % (x, y, c, len(ro)))
                (ox, oy) = ro[0]
                self.add_plane_gen(plane_gcells, gen, ox, oy)

    def add_all_planes(self, sorted_gcells):
        for sublist in spliterable(sorted_gcells, (lambda x : (x[-1] == VERTICAL_LINE_STATE))):
            if (len(sublist) > 0):
                self.add_plane(sublist)

    def add_main_variables(self, sorted_gcells):
        var_states = {DEAD_VARIABLE_STATE, LIVE_VARIABLE_STATE,
                    UNKNOWN_VARIABLE_STATE, DISJUNCTIVE_VARIABLE_STATE}

        disjunctives = []

        for (x, y, c) in sorted_gcells:
            if c in var_states:
                v = self.apply_state_to_variable(min(c, UNKNOWN_VARIABLE_STATE))
                if (c == DISJUNCTIVE_VARIABLE_STATE):
                    disjunctives.append(v)
                self.gcells[(x, y)] = v

        if (len(disjunctives) > 0):
            self.newclause(*disjunctives)

    def update_golly(self):
        invgcells = {v : k for (k, v) in self.gcells.iteritems()}
        for (v, c) in self.known_states.iteritems():
            if v in invgcells:
                (x, y) = invgcells[v]
                g.setcell(x, y, c)
        g.update()

def interpret_problem(celllist):

    if isinstance(celllist[0], int):
        if ((len(celllist) % 2) == 0): 
            celllist = map(tuple, zip(celllist[0::2], celllist[1::2]))
        else:
            while (len(celllist) % 3):
                celllist = celllist[:-1]
            celllist = map(tuple, zip(celllist[0::3], celllist[1::3], celllist[2::3]))

    celllist = sorted(celllist)
    gr = grill()
    gr.add_main_variables(celllist)
    gr.add_all_planes(celllist)
    gr.enforce_rule()

    return gr


def yn2bool(s):
    s = s.lower()
    if s[0] == 'y':
        return True
    elif s[0] == 'n':
        return False
    else:
        raise ValueError('%s is neither yes nor no' % s)

def golly_main():

    bounding_box = g.getrect()

    g.show('Installing rule file...')
    src_rule = os.path.join(scriptdir, 'grills-examples', 'Grills.rule')
    dst_rule = os.path.join(g.getdir('rules'), 'Grills.rule')
    shutil.copyfile(src_rule, dst_rule)
    g.show('...installed.')

    if (len(bounding_box) == 0):
        g.setrule("Grills")
        g.exit("Please draw or load an input pattern.")
    elif (g.getrule() == "Grills"):
        golly_grills()
    elif (g.getrule() == "LifeHistory"):
        golly_lhistory()
    else:
        g.exit("Pattern has the incorrect rule: '%s' != '%s'" % (g.getrule(), 'Grills'))


def threes_and_fours(i):

    bounding_box = g.getrect()
    celllist = g.getcells(bounding_box)

    while (len(celllist) % 3):
        celllist = celllist[:-1]
    celllist = map(tuple, zip(celllist[0::3], celllist[1::3], celllist[2::3]))

    return {(x, y, i): c for (x, y, c) in celllist if c in [3, 4]}


def golly_lhistory():

    ngens = int(g.getstring('How many generations to run the pattern?', '1'))

    d = threes_and_fours(0)

    g.setstep(0)
    for i in range(ngens):
        g.step()
        d.update(threes_and_fours(i + 1))

    exes = [k[0] for k in d]
    whys = [k[1] for k in d]
    zeds = [k[2] for k in d]

    minx = min(exes)
    maxx = max(exes)
    miny = min(whys)
    maxy = max(whys)

    width = (maxx - minx) + 10
    height = maxy - miny

    g.addlayer()
    g.setrule('Grills')

    for (k, v) in d.iteritems():

        x = (k[0] - minx) + (k[2] * width)
        y = k[1] - miny
        c = {3: LIVE_VARIABLE_STATE, 4: DEAD_VARIABLE_STATE}[v]
        g.setcell(x, y, c)

    for i in range(1, max(zeds) + 1):
        for j in range(height + 1):
            g.setcell(i * width - 5, j, VERTICAL_LINE_STATE)

    for i in range(max(zeds) + 1):
        g.setcell(i * width + 3, -3, ORIGIN_STATE)
        g.setcell(i * width + 3, -4, ZEROTH_GENERATION_STATE + i)


def golly_grills():

    bounding_box = g.getrect()
    celllist = g.getcells(bounding_box)

    g.show('Creating problem...')
    gr = interpret_problem(celllist)

    if gr.easy_unsat():
        g.exit('Problem is trivially unsatisfiable')

    gr.update_golly()

    solve_problem = yn2bool(g.getstring('Would you like to run the SAT solver now?', 'yes'))
    save_dimacs = solve_problem or yn2bool(g.getstring('Would you like to save a DIMACS file to solve later?', 'yes'))
    solution_file = None
    dimacs_out = None

    if save_dimacs:
        dimacs_out = g.savedialog('Save DIMACS file', 'DIMACS CNF files (*.cnf)|*.cnf', g.getdir('data'), 'problem.cnf')

    if solve_problem:
        ss = g.getstring('Please specify maximum duration (in seconds) for lingeling optimisation', '300')
        dimacs_dir = dimacs_out[:-4] + '_dir'
        g.show('Invoking lingeling for at most %s seconds...' % ss)

        simp_status = gr.write_and_simplify(dimacs_dir=dimacs_dir, dimacs_out=dimacs_out, simptime=int(ss))

        if (simp_status == 'SAT'):
            g.show('Problem is satisfiable')
            solution_file = os.path.join(dimacs_dir, 'solution.txt')
        elif (simp_status == 'UNSAT'):
            g.exit('Problem is unsatisfiable')
        else:
            g.show('Generated head and tail files.')

            if yn2bool(g.getstring('Would you like to run this in single-CPU iglucose?', 'yes')):
                g.show('Running iglucose in single-CPU mode...')
                solution_file = os.path.join(dimacs_dir, 'solution.txt')
                runbash(os.path.join(scriptdir, 'scripts', 'iglucose.sh'),
                        '-stop-at-sat',
                        os.path.join(dimacs_dir, 'full.icnf'),
                        solution_file)

    elif dimacs_out:

        gr.write_dimacs(dimacs_out)

    if solution_file is None:
        if yn2bool(g.getstring('Would you like to load a solution file?', 'yes')):
            solution_file = g.opendialog('Load SAT solution', 'All files (*)|*', g.getdir('data'))

    if solution_file:
        gr.load_solution(solution_file)
        gr.update_golly()

if within_golly:
    golly_main()
elif __name__ == '__main__':
    stderr.write('\033[31;1mYou should run this script from within Golly.\033[0m\n')

    # print list(cartesian_product(*map(enumerate, [[0, 1], [0, 2]])))
    # print list(cartesian_product(*map(lambda x : list(enumerate(x)), [[0, 1], [0, 2]])))

    pass
