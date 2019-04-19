
def parse_velocity(vs):

    orthogonal = False
    diagonal = False

    if 'd' in vs:
        diagonal = True
        vs = vs.replace('d', '')

    vs = vs.replace('o', '').replace('c', ('' if ('/' in vs) else '/'))

    num, den = vs.split('/')

    if (num == ''):
        num = 1
    else:
        num = eval(num)

    if not isinstance(num, tuple):
        if diagonal:
            num = (num, num)
        else:
            num = (num, 0)

    num = map(abs, num)

    a = min(*num)
    b = max(*num)

    return (a, b, int(den))

def xgcd(b, n):
    '''
    Extended Euclidean algorithm:
    '''
    x0, x1, y0, y1 = 1, 0, 0, 1
    while n != 0:
        q, b, n = b // n, n, b % n
        x0, x1 = x1, x0 - q * x1
        y0, y1 = y1, y0 - q * y1
    return (b, x0, y0) if (b > 0) else (-b, -x0, -y0)

def vargcd(x, y, *others):
    '''
    Variadic gcd:
    '''
    z = xgcd(x, y)[0]
    if (len(others) > 0):
        z = vargcd(z, *others)
    return z

def xgcd_l2(a, b):
    '''
    Find (g, x, y) such that ax + by = g = gcd(a, b), with (x, y) chosen to
    minimise the l2 norm:
    '''
    g, x, y = xgcd(a, b)
    while (x ** 2 + y ** 2 > (x - b) ** 2 + (y + a) ** 2):
        x -= b
        y += a
    while (x ** 2 + y ** 2 > (x + b) ** 2 + (y - a) ** 2):
        x += b
        y -= a
    return (g, x, y)

def partial_derivatives(a, b, p):

    if (p <= 0):
        raise ValueError("Period must be positive.")
    if (a < 0):
        raise ValueError("Horizontal displacement must be non-negative.")
    if (b <= 0):
        raise ValueError("Vertical displacement must be positive.")
    if (b < a):
        raise ValueError("Horizontal displacement cannot exceed vertical displacement.")
    if (vargcd(a, b, p) != 1):
        raise ValueError("Spatiotemporal offsets must be coprime.")

    dudx = vargcd(b, p)
    dvdy = p / dudx
    dvdt = b / dudx
    _, ut_a, uy_a = xgcd_l2(dvdy, -dvdt)

    return {'dudx': dudx, 'dudy': (a * uy_a), 'dudt': (a * ut_a),
            'dvdx': 0,    'dvdy': dvdy,       'dvdt': dvdt,
            'a': a, 'b': b, 'p': p}

