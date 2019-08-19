from iqpx import PartialExtender, canon6, partial_derivatives, parse_velocity, calculate_padding, trace_to_rle, \
    printint, ikpxtree, bytesToTuple, tupleToBytes, splice
import random
import signal
from sys import stdout
import multiprocessing
import os


def worker_function(name, master_queue, worker_queue, worker_root,
                    params, encoding, mintimeout=1):
    """
    The function executed by the worker threads. This receives work from
    the master thread, encodes it as a SAT problem, and delegates it down to
    the iglucose solvers (the _real_ workers!).
    """

    def raise_keyboard_interrupt(signal, frame):
        raise KeyboardInterrupt

    signal.signal(signal.SIGINT, raise_keyboard_interrupt)

    def single_work(rows, W, K, timeout):
        px = PartialExtender(W, K, rows, params)
        px.enforce_rule(encoding=encoding)
        if px.easy_unsat():
            # The problem has been deemed unsatisfiable by easy deductions
            # so it would be overkill to run a new instance of iglucose:
            return True
        else:
            # The problem may have solutions, so we run iglucose to find
            # all possible completions of the next row (within a time
            # limit to ensure things continue moving quickly):
            stages_completed, satisfied = px.exhaust(name, worker_root, master_queue, timeout=timeout)

            return (stages_completed == 2)

    def perform_work(item):
        if len(item) == 4:
            # Legacy mode:
            return single_work(*item)

    try:
        while True:
            item = worker_queue.get()

            if item is None:
                # Swallow the sentinel and exit:
                break

            if isinstance(item, basestring):
                # Return the item to the master:
                master_queue.put((name, item))
                continue

            finished = perform_work(item)
            if not finished:  # hit timeout, try again with a longer timeout
                newitem = (item[0], item[1], item[2], item[3] * 2)
            else:  # finished within timeout, try again with a higher width
                newitem = (item[0], item[1] + 2, item[2], mintimeout)
            worker_queue.put(newitem)
            master_queue.put((name, "done", item))
    except KeyboardInterrupt:
        print("SIGINT occurred on worker %s" % worker_root)
        stdout.flush()
    finally:
        worker_queue.task_done()


class BeamSearch(ikpxtree):

    def __init__(self, name, i6tuple, search_width, lookahead, jumpahead):
        super(BeamSearch, self).__init__(name, None, i6tuple, search_width, lookahead, jumpahead)
        self.found = set([])
        self.workers = []
        self.params = None
        self.master_queue = None
        self.worker_queue = None
        self.all_workers = 0

    def traceship(self, y):
        """
        Produce the entire genealogy of a tuple and splice it together to
        recover the partial head or tail.
        """
        l = len(self.i6tuple)
        x, _ = canon6(y[:l])
        while x != self.i6tuple:
            if tupleToBytes(x) not in self.preds:
                return y
            x = bytesToTuple(self.preds[tupleToBytes(x)][0])
            if isinstance(x, basestring):
                break
            y = splice(x, y, l - 1)
        return y

    def showship(self, item):
        ts = None
        # Produce a trace of the ship or partial:
        print(item)
        if ts is None:
            ts = self.traceship(item[1:])
        ts, _ = canon6(ts)

        # Strip trailing and leading zeros:
        while (len(ts) > 1) and (ts[0] == 0):
            ts = ts[1:]
        while (len(ts) > 1) and (ts[-1] == 0):
            ts = ts[:-1]

        # Ensure we haven't displayed this image before:
        print("As integer list: %s" % repr(ts))
        print("As plaintext:")
        for t in ts:
            printint(t)
        if self.params is not None:
            print("As RLE:\n")
            try:
                rle = trace_to_rle(ts, self.params)
                print(rle)
            except:
                import traceback
                traceback.print_exc()
        stdout.flush()

    def get_defaulti(self):
        tsize = calculate_padding(self.params['dvdt'], self.params['dvdx'], self.params['dvdy'])
        defaulti = tuple([(1 if (i // 2 == (tsize - 1)) else 0) for i in xrange(tsize)])
        return defaulti

    def initialize(self):
        self.master_queue = multiprocessing.Queue()
        self.worker_queue = multiprocessing.JoinableQueue()
        a, b, p = parse_velocity(velocity)
        self.params = partial_derivatives(a, b, p)

        if os.path.exists(homedir):
            print('Directory %s already exists.' % homedir)
        else:
            os.makedirs(homedir)
            print('Directory %s created.' % homedir)

        self.workers = []
        for _ in xrange(njobs):
            worker_path = os.path.join(homedir, ('worker%d' % self.all_workers))
            self.workers.append(multiprocessing.Process(target=worker_function,
                                                        args=(direc, self.master_queue, self.worker_queue, worker_path,
                                                              self.params, encoding)))
            self.all_workers += 1

        for w in self.workers:
            w.start()

        return self.master_queue, self.worker_queue

    def find_extensions(self, partials, partsize, npartials):
        try:
            self.terminate()
        except:
            pass
        self.initialize()
        for p in partials:
            trunc = truncate(p, partsize)
            i6tuple, iw = canon6(trunc)
            self.worker_queue.put((i6tuple, 2, self.lookahead, 1))

        seen = set([])
        try:
            while len(seen) < npartials:
                val = self.master_queue.get()
                if isinstance(val[1], tuple):
                    canon, width = canon6(val[1])
                    trunc = truncate(val[1], partsize)
                    canontrunc, truncwidth = canon6(trunc)
                    if canontrunc not in seen and max(canontrunc) > 0:
                        seen.add(canontrunc)
                        print(trunc)
                        search.showship(canon)
                        print("found " + str(len(seen)) + " partials")
                else:
                    print(val)
            return seen
        except KeyboardInterrupt:
            search.terminate()
            raise KeyboardInterrupt


    def terminate(self):
        for i in xrange(len(self.workers)):
            self.worker_queue.put(None)
        self.worker_queue.cancel_join_thread()


def get_defaulti_scratch(velocity):
    a, b, p = parse_velocity(velocity)
    params = partial_derivatives(a, b, p)
    tsize = calculate_padding(params['dvdt'], params['dvdx'], params['dvdy'])
    defaulti = tuple([(1 if (i // 2 == (tsize - 1)) else 0) for i in xrange(tsize)])
    return defaulti


def truncate(partial, partsize):
    initial = list(partial)[:(partsize * 3) // 2]
    return tuple(initial[-partsize:])


if __name__ == "__main__":

    njobs = 1
    homedir = "/home/exa/Documents/iqpx/beamout"
    velocity = "c/8o"
    direc = "head"
    W = 2
    K = 64
    J = 32
    encoding = "split"
    timeout = 1
    defaulti = get_defaulti_scratch(velocity)
    partsize = len(defaulti)
    search = BeamSearch(direc, defaulti, W, K, J)
    #master_queue, worker_queue = search.initialize()

    #i6tuple, iw = canon6((0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0))
    #ls = (W - iw) // 2
    #centred_i6tuple = tuple([(r << ls) for r in i6tuple])

    #worker_queue.put((i6tuple, W, K, timeout))

    beam_width = 10
    seen = {(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)}
    allstages = []
    while True:
        seen = search.find_extensions(seen, partsize, beam_width)
        print("COMPLETED STAGE")
# note to tomorrow: after len(seen) reaches beam width:
# add seen to allstages, terminate current searches (might need to outright redo all the
# initialization stuff for a clean slate), queue up work corresponding to the partials found in the previous
# stage. Truncate the solutions to 2*period rows (period rows from previous generation, period rows from
# this one), since it already doesn't enforce the rules for cells on the edge there shouldn't be an issue
# with the previous bit terminating improperly on vacuum.

# also keep track of all_seen (cross-generational). Until I find a c/8o extensible... wick? just report
# when something is found that was in all seen but not seen, afterwards exclude it (to just allow ships)
# oh, and just use rows 8-15 for determining if something's been seen before. Or period-2*period-1, more generally
# since that's just the first new physical row.
# oh, and check if exhaust is using all period new rows to determine newness, and make it do so if not

# write partials to a per-stage file as they're found

# all this functionality should be moved to BeamSearch, probably move the "starting a new stage" and "ending
# a stage" functions there early, to keep this bit reasonably tidy

# oh, and of course don't forget to LOUDLY report when a termination-in-vacuum is found (post-first-stage)
