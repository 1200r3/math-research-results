"""Exact weighted-coordinate certificates plus Decimal spectral checks for T9."""
from check_defect import F,D,dec,dot,mv,solve,perron,energy,cosh
from pathlib import Path
import json


def weighted_model(n,edges,h,name):
    edges=[(i,j,F(c)) for i,j,c in edges]
    h=list(map(F,h))
    masses=[sum(c for i,j,c in edges if v in (i,j)) for v in range(n)]
    total=sum(masses)
    u=[dec(v).sqrt() for v in masses]
    b=[[D(0)]*n for _ in range(n)]
    lap=[[F(0)]*n for _ in range(n)]
    div=[F(0)]*n
    div3=[F(0)]*n
    k2=[F(0)]*n
    for (i,j,c),x in zip(edges,h):
        b[i][j]=b[j][i]=dec(c)/(u[i]*u[j])
        lap[i][i]+=c; lap[j][j]+=c; lap[i][j]-=c; lap[j][i]-=c
        div[i]+=c*x; div[j]-=c*x
        div3[i]+=c*x**3/6; div3[j]-=c*x**3/6
        k2[i]+=c*x*x/(2*masses[i]); k2[j]+=c*x*x/(2*masses[j])
    assert all(x==0 for x in div)
    eta=[F(0)]+solve([r[1:] for r in lap[1:]],div3[1:])
    assert mv(lap,eta)==div3
    beta=[eta[j]-eta[i] for i,j,c in edges]
    k4=[F(0)]*n
    for (i,j,c),x,y in zip(edges,h,beta):
        term=c*(x*y+x**4/24)
        k4[i]+=term/masses[i]; k4[j]+=term/masses[j]
    a=dot(masses,k2)/total
    e4=dot(masses,k4)/total
    model=dict(n=n,u=u,mass=total,B=b,lambda0=F(1),edges=edges,alpha=h,h=h,name=name)
    return model,masses,lap,k2,k4,eta,a,e4


def coeff(masses,lap,f):
    n=len(masses); total=sum(masses)
    rhs=[m*x for m,x in zip(masses,f)]
    assert sum(rhs)==0
    mat=[[lap[i][j]+masses[i]*masses[j]/total for j in range(n)] for i in range(n)]
    y=solve(mat,rhs)
    assert mv(lap,y)==rhs and dot(masses,y)==0
    return dot(rhs,y)/total,y


def main():
    c4,m4,l4,k24,k44,eta4,a4,b4=weighted_model(4,[(0,1,1),(1,2,1),(2,3,1),(3,0,2)],
                                            [F(2,7),F(2,7),F(2,7),F(1,7)],'zero_diag_cycle4')
    f2=[x-a4 for x in k24]
    q4,y2=coeff(m4,l4,f2)
    assert a4==F(1,35) and q4==F(36,300125)
    assert f2==[F(-2,245),F(3,245),F(3,245),F(-2,245)]
    k23,m5,l5,k25,k45,eta5,a5,b5=weighted_model(5,[(0,2,1),(2,1,4),(0,3,4),(3,1,1),(0,4,4),(4,1,4)],
                                             [2,F(1,2),F(1,2),2,-1,-1],'zero_diag_K23')
    assert k25==[F(1,2)]*5
    assert k45==[F(3,32),F(3,32),F(-1,32),F(-1,32),F(1,4)]
    assert b5==F(3,32)
    f4=[x-b5 for x in k45]
    q8,y4=coeff(m5,l5,f4)
    assert q8==F(5,512) and y4==f4
    checks=[]
    for model,masses,order,target in [(c4,m4,4,q4),(k23,m5,8,q8)]:
        rows=[]
        for ts in ['0.2','0.1','0.05','0.025']:
            t=D(ts)
            lam,width,_=perron(model,t)
            en,div,k=energy(model,t)
            if order==8:
                exact=(D(3)/5+(164+160*cosh(D(9)*t/2)).sqrt()/45).sqrt()
                assert abs(exact-lam)<D('1e-58')
            scaled=(lam-1-en)/t**order
            rows.append(dict(t=str(t),perron=str(lam),energy=str(en),
                             scaled_defect=str(scaled),expected=str(dec(target)),
                             error=str(scaled-dec(target)),collatz_width=str(width),
                             energy_divergence=str(div)))
        errors=[abs(D(row['error'])) for row in rows]
        assert all(errors[i+1]<errors[i]/D('3.3') for i in range(3))
        checks.append(dict(name=model['name'],n=model['n'],masses=list(map(str,masses)),
                           edges=[(i,j,str(c)) for i,j,c in model['edges']],
                           h=list(map(str,model['h'])),order=order,coefficient=str(target),rows=rows))
    out=dict(status='passed',author_check_only=True,precision=80,checks=checks,
             K23_exact=dict(eta3_pinned=list(map(str,eta5)),k2=list(map(str,k25)),
                            k4=list(map(str,k45)),mean_k4=str(b5),f4=list(map(str,f4)),q8=str(q8)),
             limits='The rational certificates are exact. Decimal radical matrices and minimization are numerical checks, not interval certificates. Minimality uses the written graph classification.')
    Path('evidence/zero_diagonal_checks.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='passed',cycle4_q4=str(q4),K23_q8=str(q8),
                          orders=[4,8],dimensions=[4,5]),indent=2))


if __name__=='__main__':
    main()
