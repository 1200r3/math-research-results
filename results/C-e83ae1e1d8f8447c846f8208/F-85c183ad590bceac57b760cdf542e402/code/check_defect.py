"""Original author checks for the Perron cycle-defect candidate.

Python standard library only; no network, external code, or subprocesses.
Exact Fraction coefficients and 80-digit Decimal numerical residuals are
evidence for finite examples, not a proof of the general theorem.
"""
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
import itertools
import json
from pathlib import Path
import platform
import random
import sys
import time

getcontext().prec = 80


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def mv(a, x):
    return [dot(row, x) for row in a]


def dec(x):
    if isinstance(x, F):
        return D(x.numerator) / D(x.denominator)
    return D(x)


def solve(a, b):
    """Gaussian elimination with pivoting, preserving Fraction/Decimal type."""
    n = len(b)
    rows = [list(a[i]) + [b[i]] for i in range(n)]
    for k in range(n):
        pivot = max(range(k, n), key=lambda i: abs(rows[i][k]))
        if rows[pivot][k] == 0:
            raise ArithmeticError('singular system')
        rows[k], rows[pivot] = rows[pivot], rows[k]
        scale = rows[k][k]
        rows[k] = [v / scale for v in rows[k]]
        for i in range(n):
            if i == k:
                continue
            scale = rows[i][k]
            rows[i] = [rows[i][j] - scale * rows[k][j]
                       for j in range(n + 1)]
    return [rows[i][-1] for i in range(n)]


def make_model(u, edges, h, lam=None, name='model'):
    """u is an unnormalized rational Perron vector; c is also unnormalized."""
    u = list(map(F, u))
    n, mass = len(u), dot(u, u)
    edges = [(i, j, F(c)) for i, j, c in edges]
    rates = [sum(c for i, j, c in edges if k in (i, j)) / u[k]**2
             for k in range(n)]
    lam = F(lam) if lam is not None else max(rates) + 1
    assert min(lam - rate for rate in rates) >= 0
    b = [[F(0) for _ in u] for _ in u]
    lap = [[F(0) for _ in u] for _ in u]
    div = [F(0) for _ in u]
    h = list(map(F, h))
    for (i, j, c), x in zip(edges, h):
        b[i][j] = b[j][i] = c / (u[i]*u[j])
        lap[i][i] += c
        lap[j][j] += c
        lap[i][j] -= c
        lap[j][i] -= c
        div[i] += c*x
        div[j] -= c*x
    for i in range(n):
        b[i][i] = lam - rates[i]
    psi = [F(0)] + solve([r[1:] for r in lap[1:]], div[1:])
    alpha = [x + psi[j]-psi[i] for (i, j, c), x in zip(edges, h)]
    a = sum(c*x*x for (i, j, c), x in zip(edges, alpha))/mass
    b4 = sum(c*x**4 for (i, j, c), x in zip(edges, alpha))/(12*mass)
    k2u = [F(0) for _ in u]
    checkdiv = [F(0) for _ in u]
    for (i, j, c), x in zip(edges, alpha):
        k2u[i] += c*x*x/(2*u[i])
        k2u[j] += c*x*x/(2*u[j])
        checkdiv[i] += c*x
        checkdiv[j] -= c*x
    assert all(x == 0 for x in checkdiv)
    g = [v-a*x for v, x in zip(k2u, u)]
    assert dot(g, u) == 0
    resolvent_matrix = [[(lam if i == j else F(0))-b[i][j]
                        +u[i]*u[j]/mass for j in range(n)] for i in range(n)]
    rg = solve(resolvent_matrix, g)
    q4 = dot(g, rg)/mass
    assert q4 >= 0 and dot(rg, u) == 0
    assert mv(b, u) == [lam*x for x in u]
    return dict(name=name, n=n, u=u, mass=mass, edges=edges, h=h,
                alpha=alpha, B=b, lambda0=lam, a=a, b4=b4, g=g, Rg=rg, q4=q4)


def cosh(x):
    ex = x.exp()
    return (ex + 1/ex)/2


def sinh(x):
    ex = x.exp()
    return (ex - 1/ex)/2


def perron(model, t, edge_values=None):
    """Newton eigenpair solve; positive eigenvector and Collatz residual checked."""
    n = model['n']
    u = list(map(dec, model['u']))
    vals = model['alpha'] if edge_values is None else edge_values
    a = [[dec(v) for v in row] for row in model['B']]
    for (i, j, c), x in zip(model['edges'], vals):
        e = (t*dec(x)).exp()
        a[i][j] *= e
        a[j][i] /= e
    r, lam = u[:], dec(model['lambda0'])
    mass = dec(model['mass'])
    # A positive shifted power iteration first selects the Perron branch.
    # Undamped Newton directly from u can converge to another eigenpair at |t|=1.
    shift = dec(model['lambda0'])
    for _ in range(10000):
        ar = mv(a, r)
        ratios = [v/x for v, x in zip(ar, r)]
        if max(ratios)-min(ratios) < D('1e-8'):
            lam = dot(u, ar)/mass
            break
        nxt = [ar[i]+shift*r[i] for i in range(n)]
        norm = dot(u, nxt)/mass
        r = [x/norm for x in nxt]
    else:
        raise ArithmeticError('Perron branch initialization failed: '+model['name'])
    for iteration in range(50):
        ar = mv(a, r)
        residual = [ar[i]-lam*r[i] for i in range(n)]
        if max(map(abs, residual)) < D('1e-65'):
            break
        mat = [[a[i][j]-(lam if i == j else D(0)) for j in range(n)]
               +[-r[i]] for i in range(n)]
        mat.append(u+[D(0)])
        step = solve(mat, [-x for x in residual]+[mass-dot(u, r)])
        r = [r[i]+step[i] for i in range(n)]
        lam += step[-1]
    else:
        raise ArithmeticError('eigenpair Newton failed to converge')
    assert min(r) > 0, model['name']+' t='+str(t)
    ratios = [v/x for v, x in zip(mv(a, r), r)]
    assert max(ratios)-min(ratios) < D('1e-60')
    return lam, max(ratios)-min(ratios), iteration


def energy(model, t):
    n = model['n']
    edges = [(i, j, dec(c)) for i, j, c in model['edges']]
    h = [t*dec(x) for x in model['alpha']]
    p = [D(0)]*n

    def objective(potential):
        return sum(2*c*(cosh(x+potential[j]-potential[i])-1)
                   for (i, j, c), x in zip(edges, h))

    for iteration in range(60):
        div = [D(0)]*n
        lap = [[D(0)]*n for _ in range(n)]
        for (i, j, c), x in zip(edges, h):
            z = x+p[j]-p[i]
            flow, w = c*sinh(z), c*cosh(z)
            div[i] += flow
            div[j] -= flow
            lap[i][i] += w
            lap[j][j] += w
            lap[i][j] -= w
            lap[j][i] -= w
        if max(map(abs, div)) < D('1e-60'):
            break
        step = [D(0)]+solve([r[1:] for r in lap[1:]], div[1:])
        scale, old = D(1), objective(p)
        for _ in range(120):
            trial = [p[i]+scale*step[i] for i in range(n)]
            if objective(trial) <= old+D('1e-70'):
                p = trial
                break
            scale /= 2
        else:
            raise ArithmeticError('energy line search failed')
    else:
        raise ArithmeticError('energy Newton failed to converge')
    z = [x+p[j]-p[i] for (i, j, c), x in zip(edges, h)]
    k = [D(0)]*n
    for (i, j, c), x in zip(edges, z):
        v = c*(cosh(x)-1)
        k[i] += v/dec(model['u'][i])**2
        k[j] += v/dec(model['u'][j])**2
    return objective(p)/dec(model['mass']), max(map(abs, div)), k


def determinant(matrix):
    n = len(matrix)
    ans = D(0)
    for perm in itertools.permutations(range(n)):
        inv = sum(perm[i] > perm[j] for i in range(n) for j in range(i+1, n))
        term = D(-1 if inv % 2 else 1)
        for i in range(n):
            term *= matrix[i][perm[i]]
        ans += term
    return ans


def cubic_root(rhs, gap1, gap2):
    s = rhs/(gap1*gap2)
    for _ in range(100):
        residual = s*(s+gap1)*(s+gap2)-rhs
        if abs(residual) < D('1e-70'):
            return s
        s -= residual/(3*s*s+2*(gap1+gap2)*s+gap1*gap2)
    raise ArithmeticError('cubic failed')


def run():
    started = time.monotonic()
    leaf = make_model([1, 1, 1, 1], [(0,1,1),(1,2,1),(2,0,1),(2,3,1)],
                      [F(1,3)]*3+[0], lam=4, name='triangle_with_leaf')
    assert leaf['a'] == F(1,12)
    assert leaf['b4'] == F(1,1296)
    assert leaf['q4'] == F(11,5184)

    balanced = make_model([2,3,3], [(0,1,F(1,2)),(1,2,F(1,7)),(2,0,F(1,2))],
                          [F(2,11),F(7,11),F(2,11)], lam=1,
                          name='quartic_zero_eighth_nonzero')
    assert balanced['q4'] == 0 and balanced['a'] == F(1,242)
    # Exact prospective eighth-order coefficient from the balanced-gauge block formula.
    g4 = [F(105,4*11**5)*x for x in [3,-1,-1]]
    q8 = dot(g4, [F(36,11)*x for x in g4])/22
    assert q8 == F(99225,8*11**11)

    exact_records = []
    for model in (leaf, balanced):
        rows = []
        for ts in ['0.2','0.1','0.05','0.025']:
            t = D(ts)
            lam, residual, nit = perron(model, t)
            en, divergence, k = energy(model, t)
            if model is leaf:
                scalar = cubic_root(2*(cosh(t)-1), D(3), D(4))
                exact_en = D('1.5')*(cosh(t/3)-1)
                assert abs(en-exact_en) < D('1e-60')
                assert abs(lam-4-scalar) < D('1e-60')
                leading, order = dec(leaf['q4']), 4
            else:
                scalar = cubic_root((cosh(t)-1)/4536, D(11)/36, D(11)/126)
                assert abs(lam-1-scalar) < D('1e-60')
                leading, order = dec(q8), 8
            scaled = (lam-dec(model['lambda0'])-en)/t**order
            rows.append(dict(t=str(t), eigenvalue=str(lam), energy=str(en),
                             defect_over_t_power=str(scaled), expected=str(leading),
                             power=order, error=str(scaled-leading),
                             collatz_width=str(residual), divergence=str(divergence)))
        errors = [abs(D(row['error'])) for row in rows]
        assert all(errors[i+1] < errors[i]/D('3.5') for i in range(3))
        exact_records.append(dict(name=model['name'], a=str(model['a']),
                                  b4=str(model['b4']), q4=str(model['q4']), rows=rows))

    # Explicit tests of tree gauge invariance and homogeneous-cycle equality.
    tree = make_model([1,2,1,2], [(0,1,1),(1,2,2),(1,3,1)], [2,-1,F(3,2)], name='tree')
    cycle = make_model([1]*4, [(0,1,1),(1,2,1),(2,3,1),(3,0,1)], [F(1,4)]*4,
                       lam=2, name='period_two_cycle')
    models = [tree, cycle]
    rng = random.Random(20261025)
    for index in range(16):
        n = 3+index % 5
        pairs = {(i, i+1) for i in range(n-1)}
        for i in range(n):
            for j in range(i+2, n):
                if rng.random() < 0.42:
                    pairs.add((i, j))
        edges = [(i,j,F(rng.randint(1,4),rng.randint(1,3))) for i,j in sorted(pairs)]
        h = [F(rng.randint(-3,3),3) for _ in edges]
        u = [rng.randint(1,2) for _ in range(n)]
        models.append(make_model(u, edges, h, name='seeded_'+str(index)))
    checks = []
    for model in models:
        records = []
        for ts in ['-1','-0.2','0','0.2','1']:
            t = D(ts)
            lam, width, _ = perron(model, t)
            en, divergence, k = energy(model, t)
            assert lam-dec(model['lambda0'])-en > -D('1e-58')
            if model['q4'] == 0 and all(x == 0 for x in model['alpha']):
                assert abs(lam-dec(model['lambda0'])) < D('1e-58')
            if model is cycle:
                assert abs(lam-2*cosh(t/4)) < D('1e-58')
            # Gauge invariance uses the original, generally nonharmonic edge values.
            direct, _, _ = perron(model, t, model['h'])
            assert abs(lam-direct) < D('1e-58')
            records.append(dict(t=str(t), defect=str(lam-dec(model['lambda0'])-en),
                                collatz_width=str(width), divergence=str(divergence)))
        t = D('0.002')
        lam, _, _ = perron(model, t)
        en, _, _ = energy(model, t)
        scaled = (lam-dec(model['lambda0'])-en)/t**4
        q4 = dec(model['q4'])
        assert abs(scaled-q4) < D('0.0001')*(1+abs(q4))
        checks.append(dict(name=model['name'], n=model['n'], u=list(map(str,model['u'])),
                           edges=[(i,j,str(c)) for i,j,c in model['edges']],
                           h=list(map(str,model['h'])), alpha=list(map(str,model['alpha'])),
                           a=str(model['a']), b4=str(model['b4']), q4=str(model['q4']),
                           small_t_scaled_defect=str(scaled), rows=records))
    out = dict(status='passed', author_check_only=True, precision=getcontext().prec,
               python=sys.version, platform=platform.platform(), seed=20261025,
               exact_examples=exact_records, prospective_q8=str(q8),
               finite_graphs=len(models), global_points=5*len(models),
               checks=checks, elapsed_seconds=time.monotonic()-started,
               limitations=['Finite examples only; no universal computational proof.',
                            'Decimal residuals are not interval-arithmetic certificates.',
                            'All checks have the same author/context as the proof.'])
    path = Path('evidence/numerical_checks.json')
    path.write_text(json.dumps(out, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k:out[k] for k in ['status','precision','finite_graphs','global_points',
                                        'prospective_q8','elapsed_seconds']}, indent=2))
    for record in exact_records:
        print(record['name'], 'a=',record['a'], 'b4=',record['b4'], 'q4=',record['q4'])
        for row in record['rows']:
            print('t=',row['t'], 'scaled_defect=',row['defect_over_t_power'], 'error=',row['error'])


if __name__ == '__main__':
    run()
