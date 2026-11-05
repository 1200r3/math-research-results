"""Independent bounded checks of Perron R5. Python standard library only."""
from collections import Counter
from decimal import Decimal as D, localcontext
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, permutations, product
from math import factorial, prod
from pathlib import Path
import json
import platform
from random import Random

ROOT = Path(__file__).resolve().parent
REQ = ROOT.with_name("Perron-r5-clarified-20261105-boundary-request")
SAMPLES = {}


def verify_materials():
    request = json.loads((REQ / "request.json").read_bytes())
    material = REQ / "materials"
    expected = {row["path"]: row for row in request["materials"]}
    assert set(expected) == {p.relative_to(material).as_posix() for p in material.rglob("*") if p.is_file()}
    for name, row in expected.items():
        data = (material / name).read_bytes()
        assert len(data) == row["size"] and sha256(data).hexdigest() == row["sha256"], name
    assert expected["statement.md"]["sha256"] == request["statement_sha256"]
    return {"files": len(expected), **{k: request[k] for k in (
        "request_id", "package_id", "claim_id", "claim_revision", "manifest_sha256", "statement_sha256")}}


def exp_series(poly):
    """Coefficient recurrence from (exp P)' = P' exp P, P(0)=0."""
    assert poly[0] == 0
    out = [F(1)]
    for d in range(1, len(poly)):
        out.append(sum((j * poly[j] * out[d-j] for j in range(1, d+1) if poly[j]), F(0)) / d)
    return out


class Model:
    """B conjugated by diag(sqrt(mu)); use only rational coordinates."""
    def __init__(self, mu, edges, lam=None):
        self.mu = list(map(F, mu))
        self.n = len(mu)
        self.M = sum(self.mu)
        self.edges = [(i, j, F(c), F(h)) for i, j, c, h in edges]
        assert all(c > 0 and i != j for i, j, c, h in self.edges)
        assert len({frozenset((i,j)) for i,j,c,h in self.edges}) == len(self.edges)
        n = self.n
        self.L = [[F(0) for j in range(n)] for i in range(n)]
        for i, j, c, h in self.edges:
            self.L[i][i] += c
            self.L[j][j] += c
            self.L[i][j] -= c
            self.L[j][i] -= c
        self.lam = F(lam) if lam is not None else 1+max(self.L[i][i]/self.mu[i] for i in range(n))
        self.diag = [self.lam-self.L[i][i]/self.mu[i] for i in range(n)]
        assert min(self.mu) > 0 and min(self.diag) >= 0
        # Invert the fixed grounded Laplacian once by Gauss-Jordan.
        m = n-1
        A = [self.L[i+1][1:] + [F(i==j) for j in range(m)] for i in range(m)]
        for i in range(m):
            pivot = A[i][i]
            assert pivot > 0
            A[i] = [a/pivot for a in A[i]]
            for j in range(m):
                if j != i and (p := A[j][i]):
                    A[j] = [a-p*b for a,b in zip(A[j],A[i])]
        self.inv = [row[m:] for row in A]

    def avg(self, a):
        return sum(w*v for w,v in zip(self.mu,a))/self.M

    def solve(self, rhs, center=False):
        assert sum(rhs) == 0
        x = [F(0)] + [sum(v*b for v,b in zip(row,rhs[1:])) for row in self.inv]
        assert all(sum(a*b for a,b in zip(row,x)) == y for row,y in zip(self.L,rhs))
        if center:
            m = self.avg(x)
            x = [v-m for v in x]
        return x

    def balance(self, deg):
        z = [[F(0)] + [h] + [F(0)]*(deg-1) for _,_,_,h in self.edges]
        for d in range(1,deg+1,2):
            div = [F(0)]*self.n
            for (i,j,c,_), w in zip(self.edges,z):
                s = c*exp_series(w[:d+1])[d]  # w odd: odd terms of exp = sinh
                div[i] += s
                div[j] -= s
            phi = self.solve(div)
            for (i,j,_,_), w in zip(self.edges,z):
                w[d] += phi[j]-phi[i]
            check = [F(0)]*self.n
            for (i,j,c,_), w in zip(self.edges,z):
                s = c*exp_series(w[:d+1])[d]
                check[i] += s
                check[j] -= s
            assert not any(check), (d,check)
        local = [[F(0)]*(deg+1) for _ in self.mu]
        for (i,j,c,_), w in zip(self.edges,z):
            p = exp_series(w)
            for d in range(2,deg+1,2):  # even terms of exp = cosh
                local[i][d] += c*p[d]/self.mu[i]
                local[j][d] += c*p[d]/self.mu[j]
        return z,local,[self.avg(vals) for vals in zip(*local)]

    def perron(self, deg):
        # Use ORIGINAL edge data, no balancing or block identity in this branch.
        coeff = [None] + [[(i,j,c/self.mu[i]*h**d/factorial(d),c/self.mu[j]*(-h)**d/factorial(d))
                          for i,j,c,h in self.edges if h] for d in range(1,deg+1)]
        eig, vec = [self.lam], [[F(1)]*self.n]
        for d in range(1,deg+1):
            rhs = [F(0)]*self.n
            for j in range(1,d+1):
                for i,k,a,b in coeff[j]:
                    rhs[i] += a*vec[d-j][k]
                    rhs[k] += b*vec[d-j][i]
                if j < d and eig[j]:
                    rhs = [r-eig[j]*v for r,v in zip(rhs,vec[d-j])]
            eig.append(self.avg(rhs))
            vec.append(self.solve([(r-eig[d])*w for r,w in zip(rhs,self.mu)],center=True))
            assert self.avg(vec[-1]) == 0
        return eig

    def check(self, name, deg, expected=None, expect_zero=False):
        z, k, E = self.balance(deg)
        eig = self.perron(deg)
        delta = [F(0)] + [eig[j]-E[j] for j in range(1,deg+1)]
        assert not any(delta[1::2])
        assert not any(delta[:4])
        if deg >= 4:
            # T2 constants, checked against separate eigenvalue and energy computations.
            alpha = [w[1] for w in z]
            a = sum(c*h*h for (_,_,c,_), h in zip(self.edges,alpha))/self.M
            b = sum(c*h**4 for (_,_,c,_), h in zip(self.edges,alpha))/(12*self.M)
            assert E[2] == eig[2] == a and E[4] == b
            f = [row[2]-a for row in k]
            Rf = self.solve([w*v for w,v in zip(self.mu,f)],center=True)
            assert delta[4] == self.avg([x*y for x,y in zip(f,Rf)])
        lead = next(((d,v) for d,v in enumerate(delta) if v), None)
        v_deg = next((j for j in range(2,deg+1,2) if len(set(row[j] for row in k)) > 1),None)
        if v_deg is not None and 2*v_deg <= deg:
            f = [row[v_deg]-E[v_deg] for row in k]
            Rf = self.solve([w*v for w,v in zip(self.mu,f)],center=True)
            q = self.avg([x*y for x,y in zip(f,Rf)])
            assert lead == (2*v_deg,q) and q > 0, (name,lead,v_deg,q)
        else:
            assert lead is None, (name, lead, v_deg)
        if expected is not None:
            assert lead == expected, (name,lead,expected)
        if expect_zero:
            assert lead is None, (name,lead)
        if name:
            SAMPLES[name] = {"vertices":self.n,"edges":len(self.edges),"lambda0":str(self.lam),
                "all_diagonal_positive":min(self.diag)>0,"zero_diagonal":not any(self.diag),
                "degree":deg,"first_nonconstant_k_degree":v_deg,
                "leading":None if lead is None else [lead[0],str(lead[1])],
                "energy":{j:str(v) for j,v in enumerate(E) if v},
                "perron":{j:str(v) for j,v in enumerate(eig) if v},
                "defect":{j:str(v) for j,v in enumerate(delta) if v}}
        return lead, E, eig, k


def cycle(C, mu, h=None, lam=None, leaf=None):
    n = len(C)
    if h is None:
        s = sum(1/F(x) for x in C)
        h = [1/F(c)/s for c in C]
    edges = [(i,(i+1)%n,c,w) for i,(c,w) in enumerate(zip(C,h))]
    if leaf is not None:
        edges.append((n-1,n,*leaf))
    return Model(mu, edges, lam)


def bip_lift(model):
    n = model.n
    edges = [(i,n+i,model.mu[i]*d,0) for i,d in enumerate(model.diag) if d]
    for i,j,c,h in model.edges:
        edges.extend([(i,n+j,c,h),(n+i,j,c,h)])
    return Model(model.mu*2, edges, model.lam)


def unicyclic_checks():
    a = cycle([1,1,1],[1]*4,lam=4,leaf=(1,0))
    a.check("triangle_leaf_order4",12,(4,F(11,5184)))
    cycle([1,1,1],[1]*4,[-1,6,-5],4,leaf=(1,19)).check("triangle_leaf_zero_flux",12,expect_zero=True)
    cycle([1,1,1],[1]*4,[-1,6,-5+F(1,10**6)],4,leaf=(1,19)).check(
        "triangle_leaf_near_zero_flux",8,(4,F(11,5184*10**24)))
    cycle([1,1,2],[1]*3,lam=5).check("N1_triangle_order4",12,(4,F(2,16875)))
    cycle([F(1,2),F(1,7),F(1,2)],[4,9,9],lam=1).check(
        "N2_triangle_order8",12,(8,F(99225,8*11**11)))
    c = cycle([F(3,2),F(3,25),F(3,23),F(3,25)],[9,9,16,16],lam=1)
    expect12 = (12,F(103684,27*25**12))
    _, E, eig, _ = c.check("N3_square_order12",14,expect12)
    _, EE, eige, _ = bip_lift(c).check("Z3_square_lift_order12",14,expect12)
    assert (E,eig) == (EE,eige)
    for n, C, mu, lam, zero in [
        (5,[3]*5,[1]*5,6,True),(5,[1,3,1,3,1],[2,4,4,4,4],1,False),
        (4,[3,1,3,1],[1]*4,4,True),(6,[2,5]*3,[2]*6,F(7,2),True),
        (4,[1,1,1,2],[3,2,2,3],1,False),(4,[1,1,1,2],[3,2,2,3],3,False)]:
        expected = None if zero else (4,F(36,300125)) if n == 4 else None
        lead, *_ = cycle(C,mu,lam=lam).check(
            f"constant_diag_C{n}_lambda_{str(lam).replace('/','_')}_{C[-1]}",
            12,expected,zero)
        assert (lead is None if zero else lead[0] == 4)
    Model([1,2], [(0,1,3,13)]).check("K2_all_flux_is_gauge",12,expect_zero=True)
    Model([3,1,2], [(0,1,3,13),(1,2,F(1,19),-9)]).check(
        "P3_all_flux_is_gauge",12,expect_zero=True)


def support_enumeration():
    out = {}
    for n in range(2,6):
        by_graph = Counter()
        for mask in range(1 << (n*(n-1)//2)):
            E = [e for j,e in enumerate(combinations(range(n),2)) if mask >> j & 1]
            neighbors = [[v if i==u else u for u,v in E if i in (u,v)] for i in range(n)]
            color, queue, bip = {0:0},[0],True
            for u in queue:
                for v in neighbors[u]:
                    if v in color:
                        if color[u] == color[v]:
                            bip = False
                    else:
                        color[v] = 1-color[u]
                        queue.append(v)
            if len(color) != n:
                continue
            by_graph[f"{'bipartite' if bip else 'nonbipartite'}_edges{len(E)}"] += 1
            if n == 2 or bip and n <= 3:
                assert len(E) == n-1
            if n == 3:
                assert len(E) in (2,3)
            if bip and n == 4:
                assert len(E) == 3 or (len(E) == 4 and all(len(row)==2 for row in neighbors))
        out[n] = by_graph
    return out


def cycle_grid():
    out = {}
    for n in range(3,8):
        counts = Counter()
        for r in product(range(1,5), repeat=n):
            # If k2 is constant it forces mu_i proportional to x+y.
            pairs = [(r[i-1],r[i]) for i in range(n)]
            q = {x*x-x*y+y*y for x,y in pairs}
            f = {(x**5+y**5)//(x+y) for x,y in pairs}
            assert all((x**5+y**5)%(x+y)==0 for x,y in pairs)
            periodic = all(r[i] == r[i-2] for i in range(n))
            assert (len(q)==len(f)==1) == periodic
            if n == 3 and len(q) == 1:
                assert periodic and len(set(r)) == 1
            counts["free_mass_forced_k2_then_"+(
                "order8" if len(q)>1 else "order12" if len(f)>1 else "zero")] += 1
            # If diagonal constant, the eigenvector equation forces mu proportional to incident C.
            k2_propto = {x*y for x,y in pairs}
            assert (len(k2_propto) == 1) == periodic
            counts["constant_diagonal_"+("zero" if periodic else "order4")] += 1
        out[n] = counts
    return out


def k23_checks():
    theta = [(0,2),(2,1),(0,3),(3,1),(0,4),(4,1)]
    C = [1,4,4,1,4,4]
    h = [F(2),F(1,2),F(1,2),F(2),F(-1),F(-1)]
    mu = [9,9,5,5,8]
    m = Model(mu, [(i,j,c,w) for (i,j),c,w in zip(theta,C,h)], 1)
    _, _, eig, k = m.check("Z2_K23",12,(8,F(5,512)))
    assert [x[2] for x in k] == [F(1,2)]*5
    assert [x[4] for x in k] == [F(3,32),F(3,32),F(-1,32),F(-1,32),F(1,4)]
    # Derive spectral series directly from two-hop return: two paths flux 5/2, one -2.
    deg = len(eig)-1
    def mul(a,b):
        return [sum(a[i]*b[d-i] for i in range(d+1)) for d in range(deg+1)]
    R = mul(eig,eig)
    R[0] -= F(3,5)
    P = mul(R,R)
    assert P == [F(324,45**2)] + [
        F(160,45**2)*F(9,2)**d/factorial(d) if d%2==0 else 0 for d in range(1,deg+1)]
    # Gauge shift that changes the raw coordinates but neither energy nor eigenvalue.
    p = [F(-5),F(4,3),F(1),F(3),F(-2)]
    g = Model(mu,[(i,j,c,w+p[j]-p[i]) for i,j,c,w in m.edges],1)
    _, E, _, _ = m.check(None,8)
    _, Eg, eigg, _ = g.check("Z2_K23_gradient_shift",8,(8,F(5,512)))
    assert E==Eg and eig[:9]==eigg


def general_constructions():
    out = {}
    for m in range(1,5):
        d = {a:F(1,a*a*prod(a*a-b*b for b in range(1,m+1) if a!=b)) for a in range(1,m+1)}
        assert [sum(c*a**(2*j) for a,c in d.items()) for j in range(1,m+1)] == [0]*(m-1)+[1]
        for style in (6,7):
            colors = [list(d),list(d)] if style == 6 else [
                [a for a in d if d[a]>0], [a for a in d if d[a]<0]]
            size = [2*len(x)+1 for x in colors]
            n = sum(size)
            edges = []
            for cell,A in enumerate(colors):
                base = 0 if cell == 0 else size[0]
                for r,a in enumerate(A,1):
                    w = 1+max((-1)**cell*d[a],0) if style==6 else abs(d[a])
                    edges.extend((base+i,base+(i+r)%size[cell],w,a) for i in range(size[cell]))
            if style == 6:
                edges.extend((i,size[0]+i,1,0) for i in range(size[0]))
            else:
                w = F(8*prod(size),n**3)
                edges.extend((i,size[0]+j,w,0) for i,j in product(range(size[0]),range(size[1])))
            B = Model([1]*n,edges, 2+2*sum(1+abs(w) for w in d.values()) if style == 6 else None)
            expected = (4*m,F(1,2*factorial(2*m)**2))
            _, E, eig, _ = B.check(f"T{style}_m{m}",4*m,expected)
            L = bip_lift(B)
            assert n == (4*m+2 if style == 6 else 2*m+2) and L.n == 2*n
            assert min(B.diag)>0 and not any(L.diag)
            _, EE, eigs, _ = L.check(f"T{style}_m{m}_lift",4*m,expected)
            assert (E,eig) == (EE,eigs)
            if style == 7:
                assert all(sum(w!=0 for i,j,c,w in edges if v in (i,j)) ==
                           2*len(colors[int(v>=size[0])]) for v in range(n))
        out[m] = str(expected[1])
    # Verify all moment matrices on subsets of eight distinct positive magnitudes.
    # The determinant product comes from diag(a^2) times a Vandermonde.
    tested = 0
    for s in range(1,9):
        for A in combinations(range(1,9),s):
            x = [a*a for a in A]
            matrix = [[F(v**j) for v in x] for j in range(1,s+1)]
            det = F(1)
            for i in range(s):
                pivot = matrix[i][i]
                det *= pivot
                for j in range(i+1,s):
                    r = matrix[j][i]/pivot
                    matrix[j] = [a-r*b for a,b in zip(matrix[j],matrix[i])]
            assert det == prod(x)*prod(y-x0 for x0,y in combinations(x,2)) > 0
            tested += 1
    return {"coefficients":out,"restricted_class_moment_matrices":tested}



def finite_twist_checks():
    """For positive rational q=exp(z), prescribe rational stationary sinh currents."""
    examples = []
    for label, n, directed_cycles, q, unit_mass in [
        ("odd_uniform",5,[((0,1,2,3,4),2)],[3]*5,True),
        ("even_alternating",4,[((0,1,2,3),2)],[2,5,2,5],True),
        ("odd_nonuniform",3,[((0,1,2),2)],[2,4,3],False),
        ("leaf_large_flux",4,[((0,1,2),2)],[8,64,32,1],False),
        ("two_cycles_mixed_flux",4,[((0,1,2),2),((0,2,3),-3)],[2,3,7,4,6],True),
        ("zero_flux",4,[((0,1,2),0)],[1]*4,False),
        ("near_zero_flux",4,[((0,1,2),F(1,10**7))],[F(10001,10000)]*3+[1],False),
    ]:
        current = {}
        for ring, strength in directed_cycles:
            for i,j in zip(ring,ring[1:]+ring[:1]):
                key = tuple(sorted((i,j)))
                current[key] = current.get(key,0)+(strength if i<j else -strength)
        if label in ("leaf_large_flux","zero_flux","near_zero_flux"):
            current[(2,3)] = 0
        mu, edges, exps, div = ([1]*n if unit_mass else list(range(1,n+1))), [], [], [F(0)]*n
        for ((i,j),J), Q in zip(current.items(), q, strict=True):
            Q = F(Q)
            if J < 0 and Q != 1:
                Q = 1/Q
            if J == 0:
                assert Q == 1
                C = F(2,7)
            else:
                C = 2*J/(Q-1/Q)
            edges.append((i,j,C,0))
            exps.append(Q)
            div[i] += C*(Q-1/Q)/2
            div[j] -= C*(Q-1/Q)/2
        assert not any(div)
        model = Model(mu,edges)
        mat = [[F(i==j)*model.diag[i] for j in range(n)] for i in range(n)]
        k = [F(0)]*n
        for (i,j,C,_),Q in zip(edges,exps):
            mat[i][j] = C/mu[i]*Q
            mat[j][i] = C/mu[j]/Q
            k[i] += C/mu[i]*(Q+1/Q-2)/2
            k[j] += C/mu[j]*(Q+1/Q-2)/2
        row = [sum(a) for a in mat]
        e = model.avg(k)
        bound = model.lam+e
        assert row == [model.lam+x for x in k]
        # Arbitrarily large gauge shift, implemented as rational diagonal similarity.
        P = [F(10**(4*i)) for i in range(n)]
        raw = [[mat[i][j]*P[j]/P[i] for j in range(n)] for i in range(n)]
        assert [[raw[i][j]*P[i]/P[j] for j in range(n)] for i in range(n)] == mat
        if len(directed_cycles) == 1:
            C_energy = 0
            for (_,_,C,_), Q in zip(edges,exps):
                J = C*(Q-1/Q)/2
                root = C*(Q+1/Q)/2
                assert root**2 == C*C+J*J
                C_energy += 2*(root-C)
            assert C_energy/model.M == e
        # Decimal only proposes a positive vector. Recompute its ratio bounds in Q.
        with localcontext() as ctx:
            ctx.prec = 78
            dm = [[D(x.numerator)/D(x.denominator) for x in a] for a in mat]
            shift = min(dm[i][i] for i in range(n))
            for i in range(n):
                dm[i][i] -= shift
            v = [D(1)]*n
            for _ in range(16000 if label == "near_zero_flux" else 1400):
                w = [sum(x*y for x,y in zip(a,v)) for a in dm]
                scale = max(w)
                v = [x/scale for x in w]
        v = list(map(F,v))
        ratios = [sum(x*y for x,y in zip(a,v))/vv for a,vv in zip(mat,v)]
        low, high = min(ratios),max(ratios)
        if len(set(k)) == 1:
            assert row == [bound]*n  # all-ones eigenvector gives exact equality
            status = "exact_equality"
        else:
            assert high >= low > bound, label
            status = "exact_strict_Collatz_lower_bound"
        with localcontext() as ctx:
            ctx.prec = 8
            def brief(x):
                return str(D(x.numerator)/D(x.denominator))
            examples.append({"name":label,"status":status,"mass":mu,
                "positive_vector_for_exact_ratio_test":[str(x) for x in v],
                "exact_gap_lower_bound":str(low-bound),
                "lambda_lower_bound_minus_lambda0_E":brief(low-bound),
                "lambda_upper_bound_minus_lambda0_E":brief(high-bound)})
    return examples



def multicycle_perturbations():
    rng = Random(20261105)
    cases = Counter()
    for n in (4,5,6):
        for case in range(12):
            # Start from a spanning path, insert the two shortest extra chords,
            # and then sample further chords; keep all magnitudes rational.
            required = {(i,i+1) for i in range(n-1)} | {(0,2),(1,3)}
            support = sorted(required | {e for e in combinations(range(n),2) if rng.randrange(3)==0})
            mu = [F(rng.randrange(1,8),rng.randrange(1,6)) for _ in range(n)]
            edges = [(i,j,F(rng.randrange(1,6),rng.randrange(1,8)),
                      F(rng.randrange(-5,6),rng.randrange(1,6))) for i,j in support]
            B = Model(mu,edges)
            lead,E,eig,_ = B.check(None,6)
            cases[f"n{n}_order{lead[0] if lead else 'undetected'}"] += 1
            # Compare raw h to nontrivially changed gauges and reversed signs.
            if case in (0,1,2):
                p = [F((-1)**i*(i+1),3) for i in range(n)]
                raw = Model(mu,[(i,j,c,-h+p[j]-p[i]) for i,j,c,h in edges],B.lam)
                u,EE,eigs,_ = raw.check(None,6)
                assert (lead,E,eig) == (u,EE,eigs)
    return cases



def clarified_exposition_checks():
    # FULL_PROOF section 1: verify equivalent multiplicative sublevel
    # bounds in log coordinates, with a tiny positive conductance.
    edges = [(0,1,F(1,10**20),F(2)),(1,2,F(1,7),F(3,8)),
             (0,2,F(7,4),F(5)),(2,3,F(3),F(2,7))]
    graph = [[],[],[],[]]
    cases = 0
    for P in ([F(1)]*4,[F(1),F(1,10**12),F(10**18),F(1,11)],
              [F(1),F(10**22),F(1,10**24),F(9,4)]):
        terms = [c*((Q:=h*P[j]/P[i])+1/Q-2) for i,j,c,h in edges]
        K = sum(terms)
        for i,j,c,h in edges:
            Z = h*P[j]/P[i]
            bound = 2+K/c
            assert Z <= bound and 1/Z <= bound
            edge_bound = bound*max(h,1/h)
            assert P[j]/P[i] <= edge_bound and P[i]/P[j] <= edge_bound
        # Fixed paths from vertex 0 give global coordinate bounds.
        paths = [(),(0,),(2,),(2,3)]
        for i,path in enumerate(paths):
            B = prod((2+K/edges[e][2])*max(edges[e][3],1/edges[e][3]) for e in path)
            assert max(P[i],1/P[i]) <= B
        cases += 1

    # FULL_PROOF section 8: symbolic 4x4 permutation expansion in (lambda,q),
    # where q = exp(t/3). Every polynomial/Laurent coefficient is an integer.
    def mul(A,B):
        out = Counter()
        for (a,b),x in A.items():
            for (c,d),y in B.items():
                out[a+c,b+d] += x*y
        return {k:v for k,v in out.items() if v}
    diag = [2,2,1,3]
    M = [[{} for j in range(4)] for i in range(4)]
    for i,x in enumerate(diag):
        M[i][i] = {(1,0):1,(0,0):-x}
    for i,j,h in [(0,1,1),(1,2,1),(2,0,1),(2,3,0)]:
        M[i][j],M[j][i] = {(0,h):-1},{(0,-h):-1}
    determinant = Counter()
    twisted_permutations = []
    for p in permutations(range(4)):
        sign = (-1)**sum(p[i]>p[j] for i,j in combinations(range(4),2))
        term = {(0,0):sign}
        for i,j in enumerate(p):
            term = mul(term,M[i][j])
        determinant.update(term)
        if any(b for a,b in term):
            twisted_permutations.append(p)
    assert sorted(twisted_permutations) == [(1,2,0,3),(2,0,1,3)]
    expect = {(1,0):1}
    for root in (1,3,4):
        expect = mul(expect,{(1,0):1,(0,0):-root})
    expected = Counter(expect)
    expected.update(mul({(1,0):-1,(0,0):3},{(0,3):1,(0,-3):1,(0,0):-2}))
    assert determinant == expected

    # ZERO_DIAGONAL section 3: direct centered-vector certificate and norm.
    C,mu = [1,1,1,2],[3,2,2,3]
    B = cycle(C,mu,lam=1)
    _,k,E = B.balance(4)
    f = [row[2]-E[2] for row in k]
    assert f == [F(x,245) for x in (-2,3,3,-2)] and B.avg(f) == 0
    product = [(C[i-1]*f[i-1]+C[i]*f[(i+1)%4])/mu[i] for i in range(4)]
    assert product == [x/6 for x in f]
    squared_norm = sum(w*x*x for w,x in zip(mu,f))
    coeff = F(6,5)*squared_norm/sum(mu)
    assert squared_norm == F(60,245**2) and coeff == F(36,300125)
    return {"pinned_sublevel_rational_examples":cases,
            "determinant_coefficients":{f"lambda^{a} q^{b}":v for (a,b),v in determinant.items() if v},
            "twisted_permutations":twisted_permutations,
            "zero_diagonal_square_unnormalized_squared_norm":str(squared_norm),
            "zero_diagonal_square_defect_coefficient":str(coeff)}


def main():
    result = {"provenance":verify_materials(),"python":platform.python_version()}
    print("44 materials matched exact SHA-256 and byte length",flush=True)
    result["graph_supports"] = support_enumeration()
    result["cycle_grid"] = cycle_grid()
    print("Finished support and exact resistance-grid enumerations",flush=True)
    unicyclic_checks()
    k23_checks()
    result["multicycle_random"] = multicycle_perturbations()
    print("Finished exact rational unicyclic and K_(2,3) Taylor checks",flush=True)
    result["arbitrary_orders"] = general_constructions()
    print("Finished T6/T7 m=1..4 and their bipartite lifts",flush=True)
    result["finite_twists"] = finite_twist_checks()
    result["clarified_exposition"] = clarified_exposition_checks()
    result["series_cases"] = SAMPLES
    with (ROOT/"checks.json").open("w",encoding="utf-8") as out:
        json.dump(result,out,indent=2,sort_keys=True)
        out.write("\n")
    print("Finished all finite-twist tests; checks.json contains reproducible coefficients")


if __name__ == "__main__":
    main()




