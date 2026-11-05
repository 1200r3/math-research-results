"""Exact and Decimal checks for the sharp order-12 example; same author/context."""
from check_defect import F, D, dec, dot, mv, make_model, perron, energy, solve
import json
from pathlib import Path


def main():
    model = make_model([3,3,4,4],
                       [(0,1,F(3,2)),(1,2,F(3,25)),(2,3,F(3,23)),(3,0,F(3,25))],
                       [F(2,75),F(1,3),F(23,75),F(1,3)], lam=1,
                       name='quartic_eighth_zero_twelfth_nonzero')
    u, mass = model['u'], model['mass']
    resistances = [1/c for i,j,c in model['edges']]
    resistance_sum = sum(resistances)
    assert resistance_sum == 25 and mass == 50
    moments = []
    for power in [1,3,5]:
        vals = [(resistances[i-1]**power+resistances[i]**power)/u[i]**2
                for i in range(4)]
        moments.append(vals)
    assert len(set(moments[0])) == len(set(moments[1])) == 1
    assert len(set(moments[2])) == 2
    assert model['q4'] == 0
    avg = dot([x*x for x in u], moments[2])/mass
    g6 = [u[i]*(moments[2][i]-avg)/(16*resistance_sum**6) for i in range(4)]
    coefficient = F(161,18*25**6)
    assert g6 == [coefficient*x for x in [4,4,-3,-3]]
    rg6 = [48*x for x in g6]
    lap = [[(F(1) if i == j else F(0))-model['B'][i][j]
            for j in range(4)] for i in range(4)]
    assert mv(lap, rg6) == g6 and dot(u, rg6) == 0
    q12 = dot(g6, rg6)/mass
    assert q12 == F(103684,27*25**12)
    rows = []
    for ts in ['0.2','0.1','0.05','0.025']:
        t = D(ts)
        lam, width, _ = perron(model,t)
        en, divergence, k = energy(model,t)
        scaled = (lam-1-en)/t**12
        error = scaled-dec(q12)
        rows.append(dict(t=str(t), eigenvalue=str(lam), energy=str(en),
                         scaled_defect=str(scaled), expected=str(dec(q12)),
                         error=str(error), collatz_width=str(width),
                         divergence=str(divergence)))
    errors = [abs(D(row['error'])) for row in rows]
    assert all(errors[i+1] < errors[i]/D('3.5') for i in range(3))
    out = dict(status='passed', author_check_only=True, precision=80,
               u=list(map(str,u)), B=[[str(x) for x in r] for r in model['B']],
               alpha=list(map(str,model['alpha'])), resistances=list(map(str,resistances)),
               normalized_moments=[[str(x) for x in row] for row in moments],
               q4='0', q8='0', q12=str(q12), g6=list(map(str,g6)),
               Rg6=list(map(str,rg6)), rows=rows)
    Path('evidence/hierarchy_checks.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(out,indent=2))


if __name__ == '__main__':
    main()
