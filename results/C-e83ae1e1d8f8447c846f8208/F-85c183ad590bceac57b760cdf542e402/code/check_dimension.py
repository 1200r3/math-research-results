"""Exact rational and Decimal author checks for T7-T8; no external dependencies."""
from check_defect import F, D, dec, dot, make_model, perron, energy, cosh, sinh
import math
import json
from pathlib import Path


def model_for_order(m):
    ds = [F(2*(-1)**(m-a),math.factorial(m-a)*math.factorial(m+a))
          for a in range(1,m+1)]
    plus = [(a,d) for a,d in enumerate(ds,1) if d>0]
    minus = [(a,-d) for a,d in enumerate(ds,1) if d<0]
    lp,lm = 2*len(plus)+1,2*len(minus)+1
    n = lp+lm
    assert n == 2*m+2
    p,q = F(lp,n),F(lm,n)
    bridge = F(8*lp*lm,n**3)
    gamma = n*bridge
    assert gamma == 8*p*q
    ep,em = lm*bridge,lp*bridge
    sp,sm = sum(v for a,v in plus),sum(v for a,v in minus)
    lam = 1+max(2*sp+ep,2*sm+em)
    edges,h,seen = [],[],set()
    for offset,L,colors in [(0,lp,plus),(lp,lm,minus)]:
        for rank,(a,weight) in enumerate(colors,1):
            for i in range(L):
                tail,head = offset+i,offset+(i+rank)%L
                pair = frozenset([tail,head])
                assert pair not in seen and len(pair)==2
                seen.add(pair)
                edges.append((tail,head,weight))
                h.append(F(a))
    for i in range(lp):
        for j in range(lm):
            edges.append((i,lp+j,bridge))
            h.append(F(0))
    model = make_model([1]*n,edges,h,lam=lam,name='improved_order_'+str(4*m))
    assert model['alpha'] == h
    assert min(model['B'][i][i] for i in range(n)) >= 1
    moments = [sum(d*F(a)**(2*j) for a,d in enumerate(ds,1))
               for j in range(1,m+1)]
    assert moments == [F(0)]*(m-1)+[F(1)]
    # Exact group-contrast resolvent certificate for the leading coefficient.
    # Use unnormalized Perron vector U=1, mass n, with centered leading k.
    diff_coefficient = F(2,math.factorial(2*m))
    v = [q*diff_coefficient]*lp+[-p*diff_coefficient]*lm
    rv = [x/gamma for x in v]
    product = [lam*rv[i]-dot(model['B'][i],rv) for i in range(n)]
    assert product == v and sum(rv)==0
    leading = dot(v,rv)/n
    assert leading == F(1,2*math.factorial(2*m)**2)
    if m>1:
        assert model['q4']==0
    rows=[]
    for ts in ['0.2','0.1','0.05']:
        t = D(ts)
        d_direct = 2*sum(dec(v)*(cosh(D(a)*t)-1) for a,v in enumerate(ds,1))
        d_closed = 2*(2*sinh(t/2))**(2*m)/D(math.factorial(2*m))
        assert abs(d_direct-d_closed)<D('1e-65')
        aa = dec(gamma)+(dec(p)-dec(q))*d_closed
        defect = 2*dec(p*q)*d_closed*d_closed/((aa*aa+4*dec(p*q)*d_closed*d_closed).sqrt()+aa)
        scaled = defect/t**(4*m)
        rows.append(dict(t=str(t),scaled_defect=str(scaled),expected=str(dec(leading)),
                         error=str(scaled-dec(leading))))
    errs=[abs(D(row['error'])) for row in rows]
    assert all(errs[i+1]<errs[i]/D('3.5') for i in range(2))
    full_checks=[]
    if m in [2,3,4]:
        t = D('0.4')
        kp=2*sum(dec(v)*(cosh(D(a)*t)-1) for a,v in plus)
        km=2*sum(dec(v)*(cosh(D(a)*t)-1) for a,v in minus)
        d=kp-km
        aa=dec(gamma)+(dec(p)-dec(q))*d
        defect=2*dec(p*q)*d*d/((aa*aa+4*dec(p*q)*d*d).sqrt()+aa)
        expected=dec(lam)+dec(p)*kp+dec(q)*km+defect
        actual,width,_=perron(model,t)
        actual_energy,divergence,_=energy(model,t)
        assert abs(actual-expected)<D('1e-58')
        assert abs(actual_energy-(dec(p)*kp+dec(q)*km))<D('1e-58')
        full_checks.append(dict(dimension=n,t=str(t),perron=str(actual),quotient=str(expected),
                                collatz_width=str(width),energy_divergence=str(divergence)))
        if m==4:
            twists={}
            for (i,j,c),x in zip(edges,h):
                twists[i,j],twists[j,i]=x,-x
            lifted_edges,lifted_h=[],[]
            for i in range(n):
                for j in range(n):
                    if model['B'][i][j]>0:
                        lifted_edges.append((i,n+j,model['B'][i][j]))
                        lifted_h.append(twists.get((i,j),F(0)))
            lift=make_model([1]*(2*n),lifted_edges,lifted_h,lam=lam,name='improved_bipartite_order_16')
            assert all(lift['B'][i][i]==0 for i in range(2*n))
            lifted_value,lifted_width,_=perron(lift,t)
            assert abs(lifted_value-expected)<D('1e-58')
            full_checks.append(dict(dimension=2*n,t=str(t),perron=str(lifted_value),
                                    quotient=str(expected),collatz_width=str(lifted_width),
                                    zero_diagonal=True))
    return dict(m=m,order=4*m,dimension=n,cell_sizes=[lp,lm],
                moment_weights=list(map(str,ds)),moments=list(map(str,moments)),
                gamma=str(gamma),leading_coefficient=str(leading),rows=rows,
                full_matrix_checks=full_checks)


def main():
    instances=[model_for_order(m) for m in range(1,9)]
    small=make_model([1,1,1],[(0,1,1),(1,2,1),(2,0,2)],
                     [F(2,5),F(2,5),F(1,5)],lam=5,name='minimum_order_four')
    assert small['B']==[[F(2),F(1),F(2)],[F(1),F(3),F(1)],[F(2),F(1),F(2)]]
    assert small['g']==[F(-1,75),F(2,75),F(-1,75)]
    assert small['q4']==F(2,16875)
    rows=[]
    for ts in ['0.2','0.1','0.05']:
        t=D(ts)
        lam,width,_=perron(small,t)
        en,div,_=energy(small,t)
        scaled=(lam-5-en)/t**4
        rows.append(dict(t=str(t),scaled_defect=str(scaled),expected=str(dec(small['q4'])),
                         error=str(scaled-dec(small['q4']))))
    errors=[abs(D(row['error'])) for row in rows]
    assert all(errors[i+1]<errors[i]/D('3.5') for i in range(2))
    out=dict(status='passed',author_check_only=True,precision=80,
             finite_parameters=list(range(1,9)),instances=instances,
             smallest_order_four=dict(dimension=3,q4=str(small['q4']),rows=rows),
             limits='Global low-dimensional lower bounds use the written tree/triangle proof, not numerical enumeration. General 2m+2 optimality is restricted to the explicitly defined two-cell class.')
    Path('evidence/dimension_checks.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='passed',orders=[r['order'] for r in instances],
                          dimensions=[r['dimension'] for r in instances],
                          minimum_fourth_order_coefficient=str(small['q4']),
                          full_matrix_dimensions=[c['dimension'] for r in instances for c in r['full_matrix_checks']]),indent=2))


if __name__=='__main__':
    main()
