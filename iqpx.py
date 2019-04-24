import multiprocessing
import random
import argparse
import signal
import cPickle
import gzip
import time

from grills import *
from parserle import rle2bin
from velocities import parse_velocity, partial_derivatives
from sys import stdout
from collections import Counter

import subprocess

import numpy as np


def run_command(cmd):
    proc = subprocess.Popen(cmd, shell=True, stdin=subprocess.PIPE)
    return proc


def calculate_padding(ddt, ddx, ddy):
    """
    Finds the extent of the neighbourhood in either the u or v direction.
    This is used to calculate the length of tuples, and also to determine
    the number of blank columns to include on the left and right sides of
    the problem.
    """
    l = abs(ddx) + abs(ddy)
    return l + max(l, abs(ddt))


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

        self.full_width = W + 2 * HPADDING
        self.full_height = len(initial_rows) + 1 + K
        self.important_variables = set([])
        self.bottom_variables = set([])
        self.initial_rows = initial_rows

        p = params['p']
        a = params['a']
        dvdy = params['dvdy']
        dudy = params['dudy']
        dvdt = params['dvdt']

        self.reverse = params['reverse'] if ('reverse' in params) else False
        total_width = (self.full_width - 2 * HPADDING) * 2 + 2 * HPADDING
        for v in xrange(self.full_height):
            for u in xrange(self.full_width):
                if (u < HPADDING) or (u >= self.full_width - HPADDING):  # second condition shouldn't trigger
                    state = DEAD_VARIABLE_STATE
                elif v < len(initial_rows):
                    state = 1 << ((initial_rows[v] >> (u - HPADDING)) & 1)
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

                if (state == UNKNOWN_VARIABLE_STATE) and (v == len(initial_rows)):
                    self.important_variables.add(variable)
                if v >= (self.full_height - len(initial_rows)):
                    self.bottom_variables.add(variable)
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
                    outqueue.put((name, self.sol2rows(sol)))
                    satisfied = True
                elif sol[:5] == 'INDET':
                    running = False

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


def canon6(rows):
    """
    Takes a tuple of rows and returns a canonised version (divided by
    the highest power of 2 which divides the gcd of the rows) together
    with the number of columns necessary to store the tuple. The latter
    is used as a heuristic for deciding which branches of the search
    tree are most auspicious.
    """

    x = reduce((lambda a, b: a | b), rows, 0)
    while (x > 0) and ((x & 1) == 0):
        rows = tuple([(r >> 1) for r in rows])
        x = reduce((lambda a, b: a | b), rows, 0)
    weight = (0 if (x == 0) else (len(bin(x)) - 2))
    return rows, weight


def splice(x, y, l):
    """
    Create a new tuple from x and y by overlapping them by l elements.
    This function can left- or right-shift x and y independently to
    ensure they are compatibly normalised. This can be used iteratively
    to reconstruct a long sequence by splicing together short canonised
    sequences.
    """

    xx = reduce((lambda a, b: a | b), x[-l:], 0)
    yy = reduce((lambda a, b: a | b), y[:l], 0)

    while xx < yy:
        x = tuple([(r << 1) for r in x])
        xx = reduce((lambda a, b: a | b), x[-l:], 0)
    while yy < xx:
        y = tuple([(r << 1) for r in y])
        yy = reduce((lambda a, b: a | b), y[:l], 0)

    return x[:-l] + y


def printint(x):
    """
    Print an integer in reversed binary using asterisks for '1's and
    dots for '0's.
    """
    print(bin(x)[2:][::-1].replace('0', '.').replace('1', '*'))


class ikpxtree(object):
    """
    This represents a search tree. In a regular (front or back) search there
    will be precisely one ikpxtree; in a MITM search there are two.
    """

    def __init__(self, name, worker_queue, i6tuple, search_width, lookahead, jumpahead):

        self.name = name
        self.lastmm = 0
        self.i6tuple = i6tuple
        self.f6tuple = tuple([0 for _ in i6tuple])
        self.preds = {tupleToBytes(i6tuple): (name, 0, 0)}
        self.bestlength = 0
        self.queue = worker_queue
        self.lookahead = lookahead
        self.jumpahead = jumpahead
        self.search_width = search_width
        self.hist = Counter()

        self.last_backup_saved = 0
        self.starttime = time.time()

    def save_state(self, directory):

        backup_parity = ['odd', 'even'][self.last_backup_saved]
        backup_name = 'backup_%s_%s.pkl.gz' % (self.name, backup_parity)
        backup_path = os.path.join(directory, backup_name)

        print('Saving backup %s' % backup_name)
        stdout.flush()

        fp = gzip.open(backup_path, 'wb')
        cPickle.dump(self.preds, fp, protocol=2)
        fp.close()
        self.last_backup_saved = 1 - self.last_backup_saved

        # Remember where we kept the last backup:
        with open(os.path.join(directory, ('backup_%s_location.txt' % self.name)), 'w') as f:
            f.write('%d\n%s' % (self.last_backup_saved, backup_name))

        print('Saved backup %s' % backup_name)
        stdout.flush()

    def load_state(self, directory, modus_operandi='append', prompt_user=False):

        bkpath = os.path.join(directory, ('backup_%s_location.txt' % self.name))

        if os.path.exists(bkpath):
            print('Backup file %s found' % bkpath)
        else:
            print('Backup file %s not found' % bkpath)
            stdout.flush()
            return

        if prompt_user:
            should_resume = yn2bool(
                raw_input("Would you like to resume %s search from saved tree? [y] : " % self.name) or 'y')
            if not should_resume:
                return

        with open(bkpath, 'r') as f:
            lines = [x for x in f]

        self.last_backup_saved = int(lines[0][0])
        backup_name = lines[1]
        while backup_name[-1] == '\n':
            backup_name = backup_name[:-1]
        backup_path = os.path.join(directory, backup_name)

        fp = gzip.open(backup_path, 'rb')
        newdict = cPickle.load(fp)
        fp.close()

        npartials = len(newdict)
        key = newdict.keys()[0]
        if isinstance(key, tuple):
            print("converting backup to bytes format")
            i = 0
            newerdict = {}
            for (k, v) in newdict.iteritems():
                i += 1
                if isinstance(v[0], tuple):
                    newerdict[tupleToBytes(k)] = (tupleToBytes(v[0]), v[1], v[2])
                else:
                    newerdict[tupleToBytes(k)] = v
                if 1%10000 == 1:
                    print("converting: %d out of %d complete" % (i, npartials))
            newdict.clear()
            newdict = newerdict


        if modus_operandi == 'append':
            self.preds.update(newdict)
        else:
            raise ValueError("modus_operandi must be 'append'")

    def traceship(self, y):
        """
        Produce the entire genealogy of a tuple and splice it together to
        recover the partial head or tail.
        """
        l = len(self.i6tuple)
        x, _ = canon6(y[:l])
        while x != self.i6tuple:
            x = bytesToTuple(self.preds[tupleToBytes(x)][0])
            if isinstance(x, basestring):
                break
            y = splice(x, y, l - 1)
        return y

    def enqueue_work(self, fsegment, min_W=None, narrow=True):

        K = self.lookahead
        max_W = self.search_width

        if narrow:
            max_W -= min(self.lastmm, 4)

        fsegment, w = canon6(fsegment)

        if min_W is None:
            min_W = max_W

        # Low-memory mode:
        if max_W >= min_W:
            self.queue.put((fsegment, w, min_W, max_W, K))

    def rundict(self):

        from collections import Counter
        plengths = Counter()

        self.lastmm = 0
        for (k, v) in self.preds.iteritems():
            self.enqueue_work(bytesToTuple(k), v[2], narrow=False)
            plengths[v[1]] += 1

        plengths = [x[1] for x in sorted(plengths.items())]
        print('%s partial lengths: %s' % (self.name, plengths))
        stdout.flush()

    def adaptive_widen(self):

        self.search_width += 1
        print('Increasing %s search width to %d...' % (self.name, self.search_width))
        stdout.flush()
        self.rundict()
        print('...adaptive widening completed.')
        stdout.flush()

    def addpred(self, fsegment, isegment, w):
        if tupleToBytes(fsegment) in self.preds:
            return 0
        else:
            if tupleToBytes(isegment) not in self.preds:
                print('Warning: new initial segment found.')
                stdout.flush()
                self.preds[tupleToBytes(isegment)] = (self.name, 0, 0)
            currlength = self.preds[tupleToBytes(isegment)][1] + 1
            self.preds[tupleToBytes(fsegment)] = (tupleToBytes(isegment), currlength, w)
            self.hist[currlength] += 1
            return currlength

    def process_item(self, item, othertree=None, found=set([]), params=None, cmd=None):
        """
        The main orchestration code performed by the master thread. We keep it
        here instead of in master_function to avoid having duplicated code
        when handling both fronts and backs of spaceships.
        """

        worker_queue = self.queue

        if isinstance(item, basestring):
            if item == 'done':
                pass
            elif item == 'commence':
                self.rundict()
            elif item == 'adawide':
                self.adaptive_widen()
            elif (len(item) >= 6) and (item[:5] == 'load '):
                t = rle2bin(item[5:])
                self.engulf_partial(t, othertree=othertree, found=found)
            else:
                raise ValueError("Command '%s' not recognised." % item)
            worker_queue.task_done()
            return

        if isinstance(item[0], basestring):
            if item[0] == 'done':
                _, segment, attained_W = item
                oldpred = self.preds[tupleToBytes(segment)]
                self.preds[tupleToBytes(segment)] = (oldpred[0], oldpred[1], attained_W + 1)
                worker_queue.task_done()
            else:
                raise ValueError("Command '%s' not recognised." % item[0])
            return

        if hasattr(item[0], '__iter__'):
            # Worker was lazy and rejected the job:
            worker_queue.put(item)
            worker_queue.task_done()
            return

        self.engulf_partial(item, othertree=othertree, found=found, jumpahead=self.jumpahead, params=params, cmd=cmd)

    def engulf_partial(self, item, othertree=None, found=set([]), jumpahead=None, params=None, cmd=None):
        """
        Take a partial (sequence of integers encoding rows in binary) and
        digest it, adding new edges to the search tree and enqueueing work
        as appropriate.
        """

        worker_queue = self.queue

        completed = ('extending %ss' % self.name) if (item[-len(self.f6tuple):] == self.f6tuple) else None

        ts = None
        currlength = 0

        if jumpahead is None:
            jumpahead = len(item) - len(self.i6tuple)
        else:
            jumpahead = min(jumpahead, len(item) - len(self.i6tuple))

        for j in xrange(jumpahead):

            tuple7 = item[j:len(self.i6tuple) + j + 1]
            isegment, _ = canon6(tuple7[:-1])
            fsegment, w = canon6(tuple7[1:])

            currlength = self.addpred(fsegment, isegment, w)

            if currlength > 0:

                self.enqueue_work(fsegment, w)

                if len(self.preds) % 100 == 0:
                    try:
                        wqs = worker_queue.qsize()
                        queue_size = ' (%s queue size ~= %d)' % (self.name, wqs)
                        self.lastmm = wqs // 1000000
                    except NotImplementedError:
                        # Mac OS X
                        queue_size = ''
                    print("%d %s edges traversed%s." % (len(self.preds), self.name, queue_size))
                    stdout.flush()

                if (cmd is not None) and (self.name == 'head'):
                    tempts = self.traceship(fsegment)
                    tempts, _ = canon6(tempts)
                    rle = trace_to_rle(tempts, params)
                    cmd.stdin.write(rle)
                    cmd.stdin.flush()

                if othertree is not None:
                    # We compare the head against known tails (or vice-versa):
                    if tupleToBytes(fsegment[::-1]) in othertree.preds:
                        hts = self.traceship(fsegment)
                        tts = othertree.traceship(fsegment[::-1])[::-1]
                        ts = splice(hts, tts, len(self.i6tuple))
                        completed = 'meet-in-the-middle approach'

        showship = None

        if completed is not None:
            showship = ('Spaceship completed by %s in %d seconds' % (completed, int(time.time() - self.starttime)))
        elif currlength > self.bestlength:
            self.bestlength = currlength
            showship = ("Found partial %s of length %d." % (self.name, currlength))

        if showship is not None:
            # Produce a trace of the ship or partial:
            if ts is None:
                ts = self.traceship(item[1:])
            if self.name == 'tail':
                ts = ts[::-1]
            ts, _ = canon6(ts)

            # Strip trailing and leading zeros:
            while (len(ts) > 1) and (ts[0] == 0):
                ts = ts[1:]
            while (len(ts) > 1) and (ts[-1] == 0):
                ts = ts[:-1]

            # Ensure we haven't displayed this image before:
            if ts not in found:
                found.add(ts)
                print(showship)
                print("As integer list: %s" % repr(ts))
                print("As plaintext:")
                for t in ts:
                    printint(t)
                if params is not None:
                    print("As RLE:\n")
                    try:
                        rle = trace_to_rle(ts, params)
                        print(rle)
                        if cmd is not None:
                            cmd.stdin.write(rle)
                            cmd.stdin.flush()
                    except:
                        import traceback
                        traceback.print_exc()
                stdout.flush()

def tupleToBytes(data):
    array = np.array(data, dtype="uint32")
    return array.tobytes()

def bytesToTuple(data):
    return tuple(np.frombuffer(data, dtype="uint32"))

def master_function(master_queue, backup_directory, argdict, params, cmd):
    """
    The function executed by the master thread. It simply pops items from the
    master_queue, reads the name of the ikpxtree to which they belong ('head'
    or 'tail'), and calls the process_item method.
    """

    if isinstance(cmd, basestring):
        cmd = run_command(cmd)

    if os.path.exists(backup_directory):
        print('Directory %s already exists.' % backup_directory)
    else:
        os.makedirs(backup_directory)
        print('Directory %s created.' % backup_directory)

    # Global function variables:
    trees = {}
    found = set([])

    fgs = {'is_interrupted': False, 'is_saving': False, 'last_backup_time': time.time(), 'backup_duration': 0.0}

    def raise_keyboard_interrupt(signal, frame):
        print("Master received SIGINT.")
        stdout.flush()
        fgs['is_interrupted'] = True
        if not fgs['is_saving']:
            save_trees()

    def save_trees():
        fgs['is_saving'] = True

        start_backup_time = time.time()

        for v in trees.itervalues():
            v.save_state(backup_directory)

        fgs['last_backup_time'] = time.time()
        fgs['backup_duration'] = fgs['last_backup_time'] - start_backup_time

        print('Backup process took %.1f seconds.' % fgs['backup_duration'])
        stdout.flush()

        if fgs['is_interrupted']:
            fgs['is_saving'] = False
            raise KeyboardInterrupt
        fgs['is_saving'] = False

    signal.signal(signal.SIGINT, raise_keyboard_interrupt)

    # Create search trees:
    for (name, args) in argdict.iteritems():
        trees[name] = ikpxtree(name, *args)
        trees[name].load_state(backup_directory)

    # Determine whether running a regular or MITM search:
    if len(trees) == 2:
        othertrees = {k: [v for (l, v) in trees.iteritems() if (l != k)][0] for k in trees}
    else:
        othertrees = {k: None for k in trees}

    print("To quit the program, either Ctrl+C or run the command:")
    print("\033[31;1m kill -SIGINT -%d \033[0m" % os.getpgid(0))
    stdout.flush()

    # Process items from the master queue and delegate work:
    try:
        while True:
            origitem = master_queue.get()

            if origitem is None:
                break

            (name, item) = origitem
            trees[name].process_item(item, othertree=othertrees[name], found=found, params=params, cmd=cmd)

            if (time.time() - fgs['last_backup_time']) > max(3600, 20 * fgs['backup_duration']):
                save_trees()

    except KeyboardInterrupt:
        print("Master received KeyboardInterrupt.")
    finally:
        print("Master finished.")
        # Prevent threads from deadlocking by self-terminating:
        if cmd is not None:
            print("Waiting for command to finish...")
            cmd.stdin.flush()
            cmd.stdin.close()
            cmd.wait()
            print("...command finished.")
        os.kill(os.getpid(), signal.SIGTERM)


def worker_function(name, master_queue, worker_queue, worker_root,
                    params, diligence, timeout, encoding):
    """
    The function executed by the worker threads. This receives work from
    the master thread, encodes it as a SAT problem, and delegates it down to
    the iglucose solvers (the _real_ workers!).
    """

    def raise_keyboard_interrupt(signal, frame):
        raise KeyboardInterrupt

    signal.signal(signal.SIGINT, raise_keyboard_interrupt)

    def single_work(rows, w, W, K):
        px = PartialExtender(W, K, rows, params)
        px.enforce_rule(encoding=encoding)
        satisfied = False
        if px.easy_unsat():
            # The problem has been deemed unsatisfiable by easy deductions
            # so it would be overkill to run a new instance of iglucose:
            return False
        else:
            if px.reverse:
                # Growing things in reverse is difficult, so we don't even
                # attempt completion here:
                stages_completed = 0
            else:
                # The problem may have solutions, so we run iglucose to find
                # all possible completions of the next row (within a time
                # limit to ensure things continue moving quickly):
                stages_completed, satisfied = px.exhaust(name, worker_root, master_queue, timeout=timeout)

            if stages_completed == 0:
                # The time limit was reached without a satisfactory
                # conclusion, so we retry without the initial attempt to
                # complete the pattern:
                stages_completed, satisfied = px.exhaust(name, worker_root, master_queue, skip_complete=True,
                                                         timeout=timeout)

            return satisfied or (stages_completed < 2)

    def multiple_work(fsegment, w, min_W, max_W, K):

        # No empty work:
        min_W = max(min_W, 2)

        # We enumerate widths backwards so we can eliminate impossible tasks:
        widths = list(xrange(min_W, max_W + 1, 2))[::-1]

        for W in widths:
            i = (W - w) // 2
            rows = tuple([(r << i) for r in fsegment])
            satisfied = single_work(rows, w, W, K)

            if not satisfied:
                break

        return fsegment, max_W

    def perform_work(item):
        if len(item) == 4:
            # Legacy mode:
            single_work(*item)
            return None
        if len(item) == 5:
            # Low-memory mode:
            return multiple_work(*item)

    try:
        while True:
            item = worker_queue.get()

            if item is None:
                # Swallow the sentinel and exit:
                break

            if isinstance(item, basestring) or (random.random() > (diligence ** (item[1] - 12))):
                # Return the item to the master:
                master_queue.put((name, item))
                continue

            returned_work = perform_work(item)
            if returned_work is not None:
                master_queue.put((name, ('done',) + returned_work))
            else:
                master_queue.put((name, 'done'))
    except KeyboardInterrupt:
        print("SIGINT occurred on worker %s" % worker_root)
        stdout.flush()
    finally:
        worker_queue.task_done()


def telephone_sanitiser_function(direc, worker_queue, njobs, widenings):
    """
    Acts as a middle-manager between the master and workers, as well as
    ensuring that the interprocess communication between them is cleaned
    up correctly.

    This thread is also responsible for adaptive widening.
    """

    def raise_keyboard_interrupt(signal, frame):
        raise KeyboardInterrupt

    signal.signal(signal.SIGINT, raise_keyboard_interrupt)

    try:
        # Search at current width:
        worker_queue.put('commence')
        worker_queue.join()
        for i in xrange(widenings):
            # Search at next width:
            worker_queue.put('adawide')
            worker_queue.join()
        print('Cleaning up %d %s worker threads...' % (njobs, direc))
        stdout.flush()
        for _ in xrange(njobs):
            worker_queue.put(None)
        worker_queue.join()
        print('...done.')
    except KeyboardInterrupt:
        print('KeyboardInterrupt triggered in telephone_sanitiser.')
    finally:
        worker_queue.cancel_join_thread()
        worker_queue.close()


def horizontal_line():
    """
    Draw a bright green horizontal line of asterisks to stdout, flanked by
    a blank line before and after.
    """
    print('\n\033[32;1m' + ('*' * 64) + '\033[0m\n')
    stdout.flush()


def printrun(outstream, quantity, char):
    if quantity <= 0:
        return
    elif quantity == 1:
        tok = char
    else:
        tok = str(quantity) + char

    if len(outstream[-1]) + len(tok) > 70:
        outstream.append(tok)
    else:
        outstream[-1] += tok


def trace_to_rle(ts, params):
    dvdy = params['dvdy']
    dudy = params['dudy']
    dvdt = params['dvdt']
    a = params['a']
    p = params['p']

    gcells = {t: [] for t in xrange(p)}

    cells = [(u, v) for (v, x) in enumerate(ts) for (u, dig) in enumerate(bin(x)[2:][::-1]) if (dig == '1')]

    for (u, v) in cells:
        for t in xrange(p):
            xp = dvdy * u - dudy * v - a * t
            yq = v - t * dvdt
            if xp % p != 0:
                continue
            if yq % dvdy != 0:
                continue
            x = xp // p
            y = yq // dvdy
            gcells[t].append((y, x))

    outstream = []

    for g in gcells.values():

        if len(g) == 0:
            continue

        g = sorted(g)
        minx = min([cc[1] for cc in g])
        miny = min([cc[0] for cc in g])
        g = [(y - miny, x - minx) for (y, x) in g]
        maxx = max([cc[1] for cc in g])
        maxy = max([cc[0] for cc in g])

        outstream.append('x = %d, y = %d' % (maxx + 1, maxy + 1))
        outstream.append('')
        lastx = 0
        lasty = 0
        runlength = 0

        for (y, x) in g:

            if (y > lasty) or (x > lastx):
                printrun(outstream, runlength, 'o')
                if y > lasty:
                    printrun(outstream, y - lasty, "$")
                    lasty = y
                    lastx = 0
                if x > lastx:
                    printrun(outstream, x - lastx, 'b')
                runlength = 0
            runlength += 1
            lastx = x + 1

        printrun(outstream, runlength, 'o')
        outstream[-1] += '!\n'

    return '\n'.join(outstream)


def dict_to_rle(psets, params, homedir, cmd):
    if isinstance(cmd, basestring):
        cmd = run_command(cmd)

    backup_dir = os.path.join(homedir, 'backup')
    if not os.path.exists(backup_dir):
        raise ValueError("Backup directory does not exist.")

    pset = psets['head']

    # Prepare initial work:
    i6tuple, _ = canon6(pset['i'])
    W = pset['w']
    K = pset['k']
    J = pset['j']

    tree = ikpxtree('head', None, i6tuple, W, K, J)
    tree.load_state(backup_dir)

    for k in tree.preds:
        if k != tupleToBytes(i6tuple):
            ts = tree.traceship(bytesToTuple(k))
            rle = trace_to_rle(ts, params)
            if cmd is None:
                print(rle)
            else:
                cmd.stdin.write(rle)
                cmd.stdin.flush()

    if cmd is not None:
        cmd.stdin.close()
        cmd.wait()


def do_everything(psets, params, homedir, encoding='split', loadhead=None, cmd=None):
    """
    ...apart from reading and interpreting command-line arguments, which is
    accomplished in the function clmain().
    """

    if os.path.exists(homedir):
        print('Directory %s already exists.' % homedir)
    else:
        os.makedirs(homedir)
        print('Directory %s created.' % homedir)

    backup_dir = os.path.join(homedir, 'backup')

    print('Ensuring iglucose is installed and operational:')
    horizontal_line()

    status = runbash(os.path.join(scriptdir, 'scripts', 'iglucose.sh'), '--help')

    print('Exit status: %d' % status)

    if status != 0:
        raise ValueError('iglucose exited with status %d' % status)
    horizontal_line()

    if len(psets) == 0:
        raise ValueError("At least one head or tail thread must be specified.")
    else:
        print('Commencing search with the following parameters:')
        for (k, v) in psets.iteritems():
            print("%s search: %s" % (k, repr(v)))
        stdout.flush()

    master_queue = multiprocessing.Queue()
    argdict = {}
    workers = []
    telephone_sanitisers = []

    for (direc, pset) in psets.iteritems():
        new_params = {k: v for (k, v) in params.iteritems()}
        new_params['reverse'] = (direc == 'tail')

        # Prepare initial work:
        i6tuple, _ = canon6(pset['i'])
        W = pset['w']
        K = pset['k']
        J = pset['j']
        njobs = pset['p']

        # i6tuple, iw = canon6(i6tuple)
        # ls = (W - iw) // 2
        # centred_i6tuple = tuple([(r << ls) for r in i6tuple])
        # worker_queue.put((centred_i6tuple, iw, W, K))

        worker_queue = multiprocessing.JoinableQueue()

        if (direc == 'head') and (loadhead is not None):
            worker_queue.put('load %s' % loadhead)

        for _ in xrange(njobs):
            worker_path = os.path.join(homedir, ('worker%d' % len(workers)))
            workers.append(multiprocessing.Process(target=worker_function,
                                                   args=(direc, master_queue, worker_queue, worker_path,
                                                         new_params, pset['d'], pset['t'], encoding)))

        argdict[direc] = (worker_queue, i6tuple, W, K, J)

        telephone_sanitisers.append(multiprocessing.Process(target=telephone_sanitiser_function,
                                                            args=(direc, worker_queue, njobs, pset['a'])))

    master = multiprocessing.Process(target=master_function,
                                     args=(master_queue, backup_dir, argdict, params, cmd))

    # Swallow SIGINT:
    signal.signal(signal.SIGINT, signal.SIG_IGN)

    # Launch the threads:
    master.start()

    for w in workers:
        w.start()
    for t in telephone_sanitisers:
        t.start()
    for t in telephone_sanitisers:
        t.join()
    for w in workers:
        w.join()

    print('Cleaning up master thread...')
    stdout.flush()
    master_queue.put(None)
    master.join()
    master_queue.close()

    print('...ikpx terminated.')
    stdout.flush()


# TIM_COE_PARTIAL = (1410, 2024, 3648, 2384, 3476, 3329)
# ROKICKI_PARTIAL = (77128, 66136, 80510, 79606, 41037, 172229)
# ROKICKI_PARTIAL2 = (5084, 12556, 10565, 11629, 11970, 1170)
# ROKICKI_PARTIAL3 = (458, 390, 181, 28, 72, 336)


def parse_descriptor(s, tsize, name, default_k=None):
    if default_k is None:
        default_k = 30
    default_k = str(default_k)

    s = s.lower()
    s = ''.join([(c if (c in '0123456789.') else ((' ' + c) if (c in 'ijkpwtda') else '')) for c in s])
    s = s.split()
    d = {k[0]: k[1:] for k in s}

    defaulti = repr(tuple([(1 if (i // 2 == (tsize - 1)) else 0) for i in xrange(tsize)]))
    if 'i' not in d:
        d['i'] = defaulti
    elif d['i'] == '':
        d['i'] = raw_input("Please enter %d initial rows for %s search [%s] : " % (tsize, name, defaulti)) or defaulti
    else:
        d['i'] = '(%s,)' % d['i'].replace('.', ',')
    if 'w' not in d:
        if 'a' not in d:
            d['w'] = repr(4 + canon6(eval(d['i']))[1])
        else:
            d['w'] = raw_input("Please enter width for %s search [34] : " % name) or '34'

    if 'a' not in d:
        d['a'] = '999999'

    if 'k' not in d:
        d['k'] = raw_input("Please enter lookahead for %s search [%s] : " % (name, default_k)) or default_k

    if 'j' not in d:
        d['j'] = '(%s) // 2' % d['k']

    if 'p' not in d:
        d['p'] = raw_input("Please enter number of CPU cores for %s search [40] : " % name) or '40'

    if 't' not in d:
        d['t'] = '600'

    if 'd' not in d:
        d['d'] = '0.9'

    d = {k: eval(v) for (k, v) in d.iteritems()}

    for k in 'wkjpt':
        if not isinstance(d[k], int):
            raise TypeError('%s must be a positive *integer*.' % k)
        if d[k] < (0 if (k == 'p') else 1):
            raise ValueError('%s must be a *positive* integer.' % k)

    if not isinstance(d['i'], tuple):
        raise TypeError('Initial rows must be a %d-tuple.' % tsize)
    if len(d['i']) != tsize:
        raise ValueError('Precisely %d initial rows must be specified.' % tsize)

    if not isinstance(d['d'], float):
        raise TypeError('Diligence must be a float.')
    if (d['d'] <= 0.0) or (d['d'] > 1.0):
        raise ValueError('Diligence must be in the semiopen interval (0, 1].')

    if not isinstance(d['a'], int):
        raise TypeError('Adaptive widening parameter must be an integer.')

    return d


def clmain():
    parser = argparse.ArgumentParser(formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument('-d', '--directory', default=None, help='''
    This must be a fully-qualified path name, such as '/tmp/ikpx'. If the
    directory does not already exist, it will be created. If unspecified,
    the user will be prompted to specify the directory herself.
    ''')

    parser.add_argument('-v', '--velocity', default=None, help='''
    This can be either in Cartesian coordinates such as '(2,1)c/6' or a
    speed with direction (such as 'c/3o' or 'c/4d') for non-oblique. If a
    speed is specified without direction (such as '2c/5'), it will assume
    orthogonal. Again, the user will be prompted if unspecified.

    The velocity is canonicalised so that orthogonal spaceships point north,
    diagonal spaceships point north-west, and oblique spaceships point in a
    direction betwixt these two extremes.

    Note: as a result of the internal lattice transformation used to convert
    physical spacetime coordinates into logical coordinates, the velocity
    (a, b)c/p may only be searched if gcd(a, b, p) = 1.
    ''')

    hth = '''
    Search from the %s of the spaceship.

    This should be a string such as 'p8w34k30'. The possible specifiers are:

        p : number of cores over which to parallelise;
        w : width of search (in 'logical columns');
        k : lookahead (in 'logical rows');
        j : maximum jumpahead (in 'logical rows') -- this should be less than
            the lookahead parameter K, and defaults to floor(K/2);
        i : initial rows -- omit to auto-infer or provide an empty string to
            request user input;
        d : diligence -- exponential decay parameter alpha such that an
            item of width x is weighted by alpha^x (defaults to 0.9);
        t : timeout (in seconds) -- amount of time permitted for each
            instance of the underlying SAT solver (defaults to 600);
        a : adaptive widening -- maximum number of times to increment the
            search width to allow the search to continue.

    If neither the 'a' nor the 'w' parameters are specified, it will default
    to unlimited adaptive widening with a narrow initial width. If 'a' alone
    is specified, the user will be prompted for the initial width.'''

    parser.add_argument('-f', '--head', default=None, help=(hth % 'front'))

    hth += '''

    If both --head and --tail are specified, then ikpx will attempt a
    meet-in-the-middle search by growing from both the front and back and
    looking for compatible overlaps. Note that in this case, the number of
    cores used will be the sum of the 'p' parameters for both search halves.
    '''

    parser.add_argument('-b', '--tail', default=None, help=(hth % 'back'))

    parser.add_argument('-e', '--encoding', default='split', help='''
    Method of encoding the cellular automaton transition rules as a set of
    SAT clauses. Possibilities are:

        'knuth' : the 'sophisticated' encoding suggested by Donald Knuth in
            The Art of Computer Programming. This sums neighbour counts using
            a binary tree and involves 13 extra variables per cell.
        'split' : the default encoding, which deviates from Knuth by using a
            mixed binary/ternary tree instead of a pure binary tree. This
            involves only 8 extra variables per cell, at the expense of
            (very slightly) more clauses.
        'naive' : uses only 3 extra variables per cell, but with much more
            complex clauses.
    ''')

    parser.add_argument('-l', '--loadhead', default=None, help='''
    RLE file in ikpx format to load as an additional head.
    ''')

    parser.add_argument('-c', '--command', default=None, help='''
    If specified, RLE representations of all phases of all partials will
    be piped into the standard input of this command. This probably needs
    to be in quotes to ensure it is treated as a single argument to ikpx.
    ''')

    # args = parser.parse_args(args=["-d", "/home/exa/Documents/lifestuff/iqpx_out/iqpx_c8o_wildmyron","-v", "c/8o", "-f", "p6k50w19", "-l", "c8o_wildmyronpartial.rle"])
    #args = parser.parse_args(
    #    args=["-d", "/home/exa/Documents/lifestuff/iqpx_out/iqpx_c8o_myron_mitm", "-v", "c/8o", "-f", "p3k50w19","-b", "p3k50w19", "-l", "c8o_wildmyronpartial.rle"])
    # args = parser.parse_args(args=["-d", "/home/exa/Documents/lifestuff/iqpx_out/iqpx_c10o", "-v", "c/10o", "-f", "p6k50"])
    # args = parser.parse_args(
    #    args=["-d", "/home/exa/Documents/lifestuff/iqpx_out/iqpx_memtest_c2o", "-v", "c/2o", "-f", "p6k50"])
    # 2c/5, symmetric, widening from nothing, p6k50, front only: 2900 edges, finished in 881 seconds
    # 2c/5, symmetric, widening from nothing, p6k50, front only, offsets set to [0]: failed (did not find a ship at width 15)
    # offsets = [W - w] also failed
    # offsets = [(W - w)//2] completed, same number of edges, 496 seconds, same ship
    # stepping W by 2, no other changes: 530 sec
    # further simplifications of multiple_work: 502 sec. Leaving them in anyway, since it really shouldn't be a slowdown
    # args = parser.parse_args()

    args = parser.parse_args(
        args=["-d", "/home/exa/Documents/lifestuff/iqpx_out/iqpx_c8o_2", "-v", "c/8o", "-f", "p3k64", "-b", "p3k64"])

    horizontal_line()
    print("Incremental Spaceship Partial Extend (iqpx)")
    horizontal_line()

    directory = args.directory
    if directory is None:
        directory = raw_input("Please enter fully-qualified target directory [/tmp/ikpx] : ") or '/tmp/ikpx'

    velocity = args.velocity
    if velocity is None:
        velocity = raw_input("Please enter velocity [(2,1)c/6] : ") or '(2,1)c/6'

    psets = {}

    print("Parsing velocity...")
    a, b, p = parse_velocity(velocity)
    params = partial_derivatives(a, b, p)
    tsize = calculate_padding(params['dvdt'], params['dvdx'], params['dvdy'])
    print("Parameters: %s" % repr(params))
    stdout.flush()

    if args.head:
        psets['head'] = parse_descriptor(args.head, tsize, 'head', 6 * params['dvdy'] + 12)

    if args.tail:
        psets['tail'] = parse_descriptor(args.tail, tsize, 'tail', 8 * params['dvdy'] + 12)

    if len(psets) == 0:
        print("Neither head nor tail specified; defaulting to head.")
        psets['head'] = parse_descriptor('', tsize, 'the', 6 * params['dvdy'] + 12)

    if ('head' in psets) and (psets['head']['p'] == 0):
        dict_to_rle(psets, params, directory, args.command)
    else:
        do_everything(psets, params, directory, encoding=args.encoding, loadhead=args.loadhead, cmd=args.command)


if __name__ == '__main__':
    clmain()
