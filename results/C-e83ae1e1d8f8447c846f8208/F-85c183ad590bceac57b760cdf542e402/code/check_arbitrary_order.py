"""Exact finite checks of the general 4m-order construction; standard library."""
from check_defect import F, D, dec, make_model, perron, cosh
import math
import json
from pathlib import Path


def construct(m):
    L = 2*m+1
    nodes = [F(a*a) for a in range(1,m+1)]
    differences = []
    for a, x in enumerate(nodes):
        den = x
        for b, y in enumerate(nodes):
            if a != b:
                den *= x-y
        differences.append(1/den)
    moments = [sum(d*F(a)**(2*j) for a,d in enumerate(differences,1))
               for j in range(1,m+1)]
    assert moments == [F(0)]*(m-1)+[F(1)]
    plus = [1+max(d,0) for d in differences]
    minus = [1+max(-d,0) for d in differences]
    lam = 2+2*sum(max(p,n) for p,n in zip(plus,minus))
    edges, h, seen = [], [], set()
    for group, weights in enumerate([plus,minus]):
        for a,w in enumerate(weights,1):
            for i in range(L):
                j = (i+a) % L
                tail, head = group*L+i, group*L+j
                unordered = frozenset([tail,head])
                assert len(unordered) == 2 and unordered not in seen
                seen.add(unordered)
                edges.append((tail,head,w))
                h.append(F(a))
    for i in range(L):
        edges.append((i,L+i,F(1)))
        h.append(F(0))
    model = make_model([1]*(2*L),edges,h,lam=lam,name='order_'+str(4*m))
    assert model['alpha'] == h
    assert min(model['B'][i][i] for i in range(2*L)) >= 1
    if m > 1:
        assert model['q4'] == 0
    rows = []
    target = F(1,2*math.factorial(2*m)**2)
    for ts in ['0.2','0.1','0.05']:
        t = D(ts)
        dd = sum(dec(d)*(cosh(D(a)*t)-1) for a,d in enumerate(differences,1))
        # Rationalized evaluation avoids subtracting two numbers near one.
        defect = dd*dd/((1+dd*dd).sqrt()+1)
        scaled = defect/t**(4*m)
        rows.append(dict(t=str(t),scaled_defect=str(scaled),coefficient=str(dec(target)),
                         error=str(scaled-dec(target))))
    errors = [abs(D(r['error'])) for r in rows]
    assert all(errors[i+1] < errors[i]/D('3.5') for i in range(2))
    numeric_matrix_check = None
    if m == 4:
        t = D('0.5')
        actual,width,_ = perron(model,t)
        kp = 2*sum(dec(w)*(cosh(D(a)*t)-1) for a,w in enumerate(plus,1))
        km = 2*sum(dec(w)*(cosh(D(a)*t)-1) for a,w in enumerate(minus,1))
        expected = dec(lam)-1+(kp+km)/2+(1+((kp-km)/2)**2).sqrt()
        assert abs(actual-expected) < D('1e-58')
        numeric_matrix_check = dict(t=str(t),full_matrix_perron=str(actual),
                                    quotient_perron=str(expected),collatz_width=str(width))
        n = model['n']
        edge_map = {}
        for (i,j,c),x in zip(model['edges'],model['h']):
            edge_map[i,j],edge_map[j,i] = x,-x
        lift_edges, lift_h = [], []
        for i in range(n):
            for j in range(n):
                if model['B'][i][j] > 0:
                    lift_edges.append((i,n+j,model['B'][i][j]))
                    lift_h.append(edge_map.get((i,j),F(0)))
        lift = make_model([1]*(2*n),lift_edges,lift_h,lam=lam,name='bipartite_order_16')
        assert all(lift['B'][i][i] == 0 for i in range(2*n))
        assert lift['alpha'] == lift_h
        lifted_value,lifted_width,_ = perron(lift,t)
        assert abs(lifted_value-expected) < D('1e-58')
        numeric_matrix_check['bipartite_dimension'] = 2*n
        numeric_matrix_check['bipartite_perron'] = str(lifted_value)
        numeric_matrix_check['bipartite_collatz_width'] = str(lifted_width)
    return dict(m=m,dimension=2*L,differences=list(map(str,differences)),
                moments=list(map(str,moments)),lambda0=str(lam),order=4*m,
                coefficient=str(target),numerical_rows=rows,
                full_matrix_check=numeric_matrix_check)


def main():
    results = [construct(m) for m in range(1,7)]
    out = dict(status='passed',author_check_only=True,precision=80,
               finite_parameters=list(range(1,7)),instances=results,
               scope='Exact finite moment identities and graph construction checks; one 18x18 Perron comparison. Universal statement rests on the written proof.')
    Path('evidence/arbitrary_order_checks.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='passed',orders=[r['order'] for r in results],
                          dimensions=[r['dimension'] for r in results],
                          matrix_check=results[3]['full_matrix_check']),indent=2))


if __name__ == '__main__':
    main()
