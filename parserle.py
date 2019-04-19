

def rle2bin(f):

    if isinstance(f, basestring):
        with open(f, 'r') as x:
            t = rle2bin_core(x)
    else:
        t = rle2bin_core(f)

    while (len(t) > 1) and (t[-1] == 0):
        t = t[:-1]

    return tuple(t)


def rle2bin_core(f):

    binlist = [0]
    xp = 0
    rl = 0

    for l in f:
        if (len(l) == 0) or (l[0] == '#') or (l[0] == 'x'):
            continue
        for c in l:
            if c in '0123456789':
                rl = 10*rl + int(c)
            if c == 'b':
                rl = max(1, rl)
                xp += rl
                rl = 0
            if c == 'o':
                rl = max(1, rl)
                for i in xrange(rl):
                    binlist[-1] += (1 << xp)
                    xp += 1
                rl = 0
            if c == '$':
                rl = max(1, rl)
                binlist += [0]*rl
                rl = 0
                xp = 0
            if c == '!':
                return binlist

    return binlist
        
