from uniquefather import PredecessorSearch
from parserle import *
from grills import *
import numpy as np

def rletoarr(rle, pad, padvert=None):
    if padvert is None:
        padvert = pad
    parse = rle2bin_core(rle)
    parse = [bin(x) for x in parse]
    parse = [x[2:] for x in parse]
    maxlen = max([len(x) for x in parse])
    res = np.zeros((len(parse) + pad*2, maxlen + padvert*2))
    parse = [x[::-1] for x in parse]
    for i, p in enumerate(parse):
        for j, c in enumerate(p):
            res[i + pad, j + padvert] = int(c)
    return res

def arrtocelllist(arr):
    result = {}
    for i in range(arr.shape[0]):
        for j in range(arr.shape[1]):
            if arr[i, j]:
                result[(i, j)] = LIVE_VARIABLE_STATE
            else:
                result[(i, j)] = DEAD_VARIABLE_STATE
    return result


if __name__ == "__main__":
    code = "18bo$17b3o$12b3o4b2o$11bo2b3o2bob2o$10bo3bobo2bobo$10bo4bobobobob2o$12bo4bobo3b2o$4o5bobo4bo3bob3o$o3b2obob3ob2o9b2o$o5b2o5bo$bo2b2obo2bo2bob2o$7bobobobobobo5b4o$bo2b2obo2bo2bo2b2obob2o3bo$o5b2o3bobobo3b2o5bo$o3b2obob2o2bo2bo2bob2o2bo$4o5bobobobobobo$10b2obo2bo2bob2o2bo$13bo5b2o5bo$b2o9b2ob3obob2o3bo$2b3obo3bo4bobo5b4o$2b2o3bobo4bo$2b2obobobobo4bo$5bobo2bobo3bo$4b2obo2b3o2bo$6b2o4b3o$7b3o$8bo!"
    #code = "4bo$2obobo$bobo2bo$o2bob2o$2obo$3bo$3o$o!"
#     code = """18b3o$14bo3bo2bo$13b3ob2o3bo$12b2o3bob2ob2o$11b2o2bo2bobobobo$12bo3bob
# obo3b2o$2b2o7b2o5bobobo3bo$b5o3b2obobo8bo$2ob4obobobob2o9b2o$b2o5bobob
# obobo$6bobo2bo2bob2o7b2o$8bobobobobob2o3b5o$6bobo2b2obobobobob4ob2o$b
# 2o5bobobobobobobo5b2o$2ob4obobobobob2o2bobo$b5o3b2obobobobobo$2b2o7b2o
# bo2bo2bobo$12bobobobobo5b2o$2b2o9b2obobobob4ob2o$5bo8bobob2o3b5o$2bo3b
# obobo5b2o7b2o$3b2o3bobobo3bo$4bobobobo2bo2b2o$5b2ob2obo3b2o$6bo3b2ob3o
# $7bo2bo3bo$8b3o!
# """.replace("\n", "")
    arr = rletoarr(code, 4)
    print(arr)
    print("""rewind 4
                                                    if t == 0 and (y == 2 or abs(y - n + 1) == 2):
                            state = DEAD_VARIABLE_STATE
                        if t == 0 and (x == 2 or abs(x - m + 1) == 2 or x == 3):
                            state = DEAD_VARIABLE_STATE""")
    cells = arrtocelllist(arr)
    search = PredecessorSearch(arr.shape[0], arr.shape[1], 2, cells, stilllife=False, allunknown=True, rewindby=4)
    npreds, pred = search.exhaust("test%d" % os.getpid(), "test%d" % os.getpid(), timeout=10000000, findany=False)
    print("npreds", npreds)
    search.printsol(pred)