import golly as g
from velocities import partial_derivatives, parse_velocity

def main():

    g.setstep(0)
    g.setalgo('QuickLife')

    velocity = g.getstring('Please specify velocity', '(2,1)c/6')
    a, b, p = parse_velocity(velocity)
    params = partial_derivatives(a, b, p)

    dvdy = params['dvdy']
    dudy = params['dudy']
    dvdt = params['dvdt']

    cells = g.getcells(g.getrect())
    cells = zip(cells[::2], cells[1::2])
    gcells = []

    for (u, v) in cells:
        for t in xrange(p):
            xp = dvdy * u - dudy * v - a * t
            yq = v - t * dvdt
            if (xp % p != 0):
                continue
            if (yq % dvdy != 0):
                continue
            x = xp // p
            y = yq // dvdy
            gcells.append((t, x, y))

    spacing = max([x for (_, x, _) in gcells]) - min([x for (_, x, _) in gcells])
    spacing += 10

    gcells = [(x + spacing * t, y) for (t, x, y) in gcells]

    g.setlayer(g.addlayer())
    g.putcells([x for y in gcells for x in y])
    g.fit()

main()
