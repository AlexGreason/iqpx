import golly as g
from velocities import partial_derivatives, parse_velocity

def main():

    g.setstep(0)
    g.setalgo('QuickLife')

    velocity = g.getstring('Please specify velocity', '(2,1)c/6')
    a, b, p = parse_velocity(velocity)
    params = partial_derivatives(a, b, p)

    dvdx = params['dvdx']
    dudx = params['dudx']
    dvdy = params['dvdy']
    dudy = params['dudy']
    dvdt = params['dvdt']
    dudt = params['dudt']

    cells = []

    for t in xrange(p):

        things = g.getcells(g.getrect())
        things = zip(things[::2], things[1::2])
        cells += [(dudx * x + dudy * y + dudt * t,
                    dvdx * x + dvdy * y + dvdt * t) for (x, y) in things]
        g.step()

    g.setlayer(g.addlayer())
    g.putcells([x for y in cells for x in y])

main()
