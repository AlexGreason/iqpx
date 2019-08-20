from iqpx import PartialExtender, canon6, partial_derivatives, parse_velocity, calculate_padding, trace_to_rle, \
    printint, ikpxtree, bytesToTuple, tupleToBytes, splice
import random
import signal
from sys import stdout
import multiprocessing
import os


def worker_function(name, master_queue, worker_queue, worker_root,
                    params, encoding, mintimeout):
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
                worker_queue.task_done()
                print("Got termination sentinel, returning")
                os._exit(0)
                return

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

    def initialize(self, njobs, timeout=1):
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
                                                              self.params, encoding, timeout)))
            self.all_workers += 1

        for w in self.workers:
            w.start()

        return self.master_queue, self.worker_queue

    def find_extensions(self, partials, partsize, npartials, njobs, head=False):
        try:
            self.terminate()
        except:
            pass
        timeout = 1
        if head:
            timeout = 300
        self.initialize(njobs, timeout)

        for p in partials:
            trunc = truncate(p, partsize)
            i6tuple, iw = canon6(trunc)
            print(i6tuple)
            self.worker_queue.put((i6tuple, self.search_width, self.lookahead, timeout))

        seen = set([])
        try:
            while len(seen) < npartials:
                val = self.master_queue.get()
                if isinstance(val[1], tuple):
                    canon, width = canon6(val[1])
                    rows = list(val[1])
                    truncated = 0
                    while (len(rows) > 1) and (rows[0] == 0) and head and truncated < partsize//2:
                        rows = rows[1:]
                        truncated += 1
                    rows = tuple(rows)
                    trunc = truncate(rows, partsize)
                    canontrunc, truncwidth = canon6(trunc)
                    if canontrunc not in seen and max(canontrunc) > 0:
                        self.engulf_partial(canon, params=self.params)
                        seen.add(canontrunc)
                        if len(seen) <= 4:
                            print(val)
                            print(trunc)
                            search.showship(canon)
                        print("found " + str(len(seen)) + " partials")
                else:
                    if isinstance(val[2], tuple):
                        timeout = val[2][3]
                        if timeout >= 8:
                            print(val)
            self.save_state(homedir)
            return seen
        except KeyboardInterrupt:
            search.terminate()
            raise KeyboardInterrupt

    def anyalive(self):
        for w in self.workers:
            if w.is_alive():
                return True
        return False

    def terminate(self):
        try:
            while not self.worker_queue.empty():
                val = self.worker_queue.get_nowait()
        except:
            pass
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

    njobs = 2
    homedir = "/home/exa/Documents/iqpx/beamout"
    velocity = "3c/11o"
    direc = "head"
    W = 1
    K = 72
    J = 32
    beam_width = 32
    head_num = 32
    encoding = "split"
    timeout = 1
    defaulti = get_defaulti_scratch(velocity)
    partsize = len(defaulti)
    search = BeamSearch(direc, defaulti, W, K, J)

    seen = {defaulti}
    stagenum = 0
    seen = search.find_extensions(seen, partsize, head_num, njobs, head=True)
    print("COMPLETED STAGE ", stagenum)
    stagenum += 1
    while True:
        seen = search.find_extensions(seen, partsize, beam_width, njobs, head=False)
        print("COMPLETED STAGE ", stagenum)
        stagenum += 1

# TODO: write partials to a file as they're found
