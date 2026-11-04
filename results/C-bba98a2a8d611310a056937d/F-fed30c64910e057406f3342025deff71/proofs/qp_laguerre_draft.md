# Periodic boundary coefficients in discrete Laguerre inequalities

Unreviewed proof manuscript. Every statement below is a candidate result until the required independent reviews are closed. No numerical experiment is used as an infinite proof.

## 1. Definitions and scope

For an integer d>=1 and a real sequence f, define the forward discrete Laguerre transform

T_d(f)(n) = sum_{j=0}^{2d} (-1)^(j+d) binom(2d,j) f(n+j) f(n+2d-j).

Its centered version, evaluated at t=n+d, is

H_d(f)(t) = sum_{j=-d}^{d} w_j f(t+j) f(t-j),
where w_j=(-1)^j binom(2d,d+j).

Thus T_d(f)(n)=H_d(f)(n+d). The inequality is T_d(f)(n)>=0. We use the words strict and non-strict explicitly. A quasi-polynomial of period M is specified by polynomials f_0(X),...,f_(M-1)(X), with f(n)=f_r(n) for n congruent to r modulo M. Indices on periodic vectors are interpreted modulo M. Write

Delta b(t)=2b(t)-b(t-1)-b(t+1).

The principal result concerns exact quasi-polynomials, not arbitrary sequences with an unspecified little-o error. This restriction permits explicit thresholds. No classification of arbitrary quasi-polynomial-like errors is claimed.

## 2. Candidate boundary-coefficient identity

Let d>=1, ell>=2d, and let P be a real polynomial of degree ell and leading coefficient a>0. Suppose

f_r(X)=P(X)+b_r X^(ell-2d)+Q_r(X),

where deg Q_r<=ell-2d-1. When ell=2d, this means Q_r=0. Let s=2ell-2d. Then the residue polynomial of T_d(f) has degree at most s, and its coefficient of X^s on residue r is

gamma_r=(2d)! binom(ell,d)a^2+2a Delta^d b(r+d).                 (2.1)

For every 1<=j<d, the transform T_j(f) has positive, residue-independent leading coefficient `(2j)! binom(ell,j)a^2` and degree 2ell-2j.

### Proof

The generating identity

sum_{j=-d}^{d} w_j exp(jz) = (2-2cosh z)^d
                          = (-1)^d z^(2d)+O(z^(2d+2))

is a finite binomial identity followed by a formal power-series expansion. Consequently the weighted sum of any polynomial in j of degree less than 2d is zero, and

sum_j w_j j^(2d)=(-1)^d(2d)!.                                 (2.2)

In P(t+j)P(t-j), the coefficient of t^k is a polynomial in j of degree at most 2ell-k. All coefficients with k>2ell-2d therefore vanish after weighted summation. At k=2ell-2d, terms involving a lower-degree monomial of P have j-degree less than 2d and also vanish. The leading monomial contributes

a^2(t+j)^ell(t-j)^ell=a^2(t^2-j^2)^ell.

Its coefficient at t^(2ell-2d) is a^2(-1)^d binom(ell,d)j^(2d). Applying (2.2) gives the first term of (2.1).

Put R(t)=f(t)-P(t). On a fixed residue class, R(t+j) has leading term b(t+j)t^(ell-2d). In the cross terms P(t-j)R(t+j)+P(t+j)R(t-j), the coefficient at t^s is a[b(t+j)+b(t-j)]. Since w_j=w_(-j), their weighted sum is `2a sum_j w_j b(t+j)`. The finite binomial identity `Delta^d=(2-E-E^(-1))^d`, with E the cyclic shift, identifies this sum with 2a Delta^d b(t). Products of two R terms have degree at most 2ell-4d<s; terms involving Q have degree at most s-1. Replacing t by n+d preserves the leading coefficient and replaces its residue by r+d. This proves (2.1).

For order j<d, the first periodic term has degree ell-2d<ell-2j, so it contributes below the smooth leading degree. The same calculation proves the final assertion. All polynomial degree comparisons include ell=2d and d=1. End of proof.

## 3. Explicit sign bounds and certificates

For a nonzero real polynomial h(X)=c_k X^k+...+c_0, define

B(h)=1+ceil((sum_{i=0}^{k-1}|c_i|)/|c_k|).                    (3.1)

For k=0 the empty sum is zero. For every real X>=B(h), h(X) has the sign of c_k: if k>=1 and S=sum_{i<k}|c_i|, the lower terms have absolute value at most S X^(k-1), whereas |c_k|X^k>S X^(k-1), because X>S/|c_k| and X>=1. For k=0 the conclusion is immediate.

For rational input quasi-polynomials, compute the exact residue polynomial

h_r(X)=sum_{j=0}^{2d}(-1)^(j+d)binom(2d,j)
                  f_((r+j) mod M)(X+j)f_((r+2d-j) mod M)(X+2d-j).    (3.2)

This gives a finite, exact decision procedure for eventual sign. A zero h_r is identically zero on that residue. Each nonzero h_r is eventually positive or negative according to its leading coefficient, with the explicit bound B(h_r). For a single order define the common bound explicitly as `N=max({1} union {B(h_r): h_r is nonzero})`. For simultaneous orders 1,...,d use `N=max({1} union {B(h_(j,r)): 1<=j<=d and h_(j,r) is nonzero})`. Thus N=1 when all output polynomials vanish; zero polynomials retain their separate zero-sign designation and do not count as strictly positive. The formulas also specify a certificate: exact input coefficient vectors, exact output vectors in (3.2), the leading signs, and the integers (3.1). Each assertion can be checked using rational polynomial arithmetic and integer inequalities.

In particular, if every gamma_r in (2.1) is positive, T_d(f) is strictly positive after this explicit bound. If some gamma_r is negative, it is strictly negative at every sufficiently large n in that residue, hence infinitely often. A zero gamma_r does not justify any sign conclusion without inspecting the lower coefficients. This elementary sign procedure is not claimed by itself as a novel result.

## 4. A restricted-partition family

Fix integers d>=1 and m>=2, put q=2d, and define p_(d,m)(n) by

sum_{n>=0}p_(d,m)(n)z^n=1/((1-z)^q(1-z^m)).                  (4.1)

Equivalently, it counts partitions using q differently colored parts of size 1 and one part of size m. Directly,

p_(d,m)(n)=sum_{v=0}^{floor(n/m)} binom(n-mv+q-1,q-1).        (4.2)

There is an exact decomposition p_(d,m)(n)=P(n)+b(n), with P a degree-q polynomial of leading coefficient

a=1/(m q!),                                                  (4.3)

and b periodic of period m. The following rational construction makes the decomposition explicit. Set u_0=1/m, and for 1<=h<=q let

u_h=-(1/m) sum_{k=1}^{min(h,m-1)}(-1)^k binom(m,k+1)u_(h-k).

Then

P(X)=sum_{h=0}^q u_h binom(X+q-h,q-h),                        (4.4)
b(r)=binom(r+q-1,q-1)-P(r),  0<=r<m.                        (4.5)

Here each binomial in X denotes its polynomial expansion.

### Proof of the decomposition

Write S_m(z)=1+z+...+z^(m-1). Then S_m(1-y)=sum_{k=0}^{m-1}(-1)^k binom(m,k+1)y^k. The u_h are exactly the first q+1 Taylor coefficients of 1/S_m(1-y), by formal multiplication. Since (4.1) equals `(1-z)^(-q-1)/S_m(z)`, its principal part at z=1 is `sum_{h=0}^q u_h(1-z)^(-q-1+h)`. Coefficient extraction gives (4.4) and (4.3).

Every remaining pole is a nontrivial mth root of unity zeta and is simple. Its partial-fraction term is

1/[m(1-zeta)^q] * 1/(1-z/zeta).

Indeed, multiplying (4.1) by 1-z/zeta and taking z to zeta gives 1/[m(1-zeta)^q]. Both rational functions are proper and the displayed principal parts account for all poles, so there is no polynomial remainder. Consequently

b(t)=(1/m) sum_(zeta^m=1,zeta!=1) zeta^(-t)/(1-zeta)^q.       (4.6)

This proves periodicity. For 0<=r<m, (4.2) has only v=0, which proves (4.5). The expressions are real (and (4.5) rational) despite the auxiliary complex formula. End of proof.

Since Delta acts on zeta^(-t) by multiplication by `2-zeta-zeta^(-1)=-(1-zeta)^2/zeta`, (4.6) gives

Delta^d b(t)=((-1)^d/m)(m*1_(m divides t+d)-1).                (4.7)

The sum of all mth roots raised to a fixed integer power is m if that power is divisible by m and zero otherwise; subtract the root 1 to obtain (4.7). Thus the coefficient of n^q in T_d(p_(d,m))(n) is

[binom(2d,d)+2(-1)^d(m*1_(m divides n+2d)-1)]/[m^2(2d)!].    (4.8)

This formula is an identity, not a finite numerical observation.

## 5. Candidate complete eventual classification for the family

For d>=2 and m>=2, all inequalities T_j(p_(d,m))(n)>0, 1<=j<=d, hold for every integer n beyond an explicitly computable bound if and only if either

- d is even; or
- d is odd and m<=1+binom(2d,d)/2.                            (5.1)

If d is odd and m>1+binom(2d,d)/2, then T_d is negative at every sufficiently large n with n+2d divisible by m. The bound in each assertion is obtained by (4.4)--(4.5), (3.2), and (3.1), using the actual leading nonzero coefficient; it is finite and contains no unspecified constant.

### Noncritical cases

For j<d, Section 2 gives a positive leading coefficient independent of the residue. For even d>=2, the two numerators in (4.8) are binom(2d,d)-2 and binom(2d,d)+2(m-1), both positive. For odd d, the numerators are binom(2d,d)+2 and binom(2d,d)-2(m-1). These settle all cases except equality in the second numerator. The central binomial coefficient is even because binom(2d,d)=2binom(2d-1,d-1), so the critical m is an integer.

### The critical odd case

Suppose d>=3 is odd, C=binom(2d,d), and m=1+C/2. Put sigma=(q+m)/2 and x=t+sigma. The polynomial part has the centered expansion

P(t)=a x^q+c x^(q-2)+terms of degree at most q-4,
c=-a q(q-1)(q+m^2)/24.                                     (5.2)

To verify (5.2), the polynomial part is minus the residue at z=1 of `(1-z)^(-q)(1-z^m)^(-1)z^(-t-1)`. Substitute z=exp(-v). Formal residue invariance yields

P(t)=(1/m)[v^q] exp((t+sigma)v)
           (v/(2sinh(v/2)))^q (mv/(2sinh(mv/2))).

The product following the exponential is even and equals `1-(q+m^2)v^2/24+O(v^4)`. Taking coefficients proves (5.2), with a as in (4.3). This also follows by expanding (4.4); the residue expression is used only as an algebraic coefficient calculation.

Consider a residue with t+d divisible by m. Define

B_k=sum_{j=-d}^d w_j j^k b(t+j).

For this residue,

B_0=-(m-1)/m,
B_1=0,
B_2=((m-1)/m)(-d^2+d(2d-1)(m+1)/6).                       (5.3)

The first identity is (4.7). For the other two, let `S(z)=(2-z-z^(-1))^d=(-1)^d(1-z)^q z^(-d)` and `D=z d/dz`. In (4.6), zeta^(-t)=zeta^d on this residue. Since `DS/S=-d(1+z)/(1-z)` and

D^2S/S=d^2+(4d^2-2d)z/(1-z)^2,

the Fourier expression for B_1 is a constant multiple of `sum_(zeta!=1)(1+zeta)/(1-zeta)`, which is zero by pairing inverse roots. For B_2, use

sum_(zeta^m=1,zeta!=1) zeta/(1-zeta)^2=-(m^2-1)/12.           (5.4)

For completeness, the logarithmic derivative of S_m(z)=prod_(zeta!=1)(z-zeta) at 1 gives sum 1/(1-zeta)=(m-1)/2 and sum 1/(1-zeta)^2=(m-1)(5-m)/12; subtracting these proves (5.4). Multiplying D^2S by (4.6) now gives (5.3). The sign in B_1 is immaterial to its zero value; D acting on zeta^(-j) introduces -j, while D^2 introduces j^2.

The coefficient of x^q in H_d(P+b) is zero by the critical relation. There is no x^(q-1) term: the polynomial part is even in x, and the only possible cross term is a multiple of B_1. The coefficient beta of x^(q-2) equals

beta = a^2 q! C d(m^2-4d^2)/12
       +2a binom(q,2)B_2+2cB_0.                             (5.5)

Here the first term is the coefficient from H_d(P). To check it directly, expand the finite moment generating function one term further:

sum_j w_j exp(jz)=(-1)^d z^q(1+d z^2/12+O(z^4)).

The a^2 contribution to x^(q-2) is `-a^2 binom(q,d+1)(q+2)!d/12`. The 2ac contribution is `2ac q![binom(q-2,d)-binom(q-2,d-1)]`. Substituting (5.2), `binom(q,d+1)=Cd/(d+1)`, and `binom(q-2,d-1)=Cd/[2(2d-1)]` reduces their sum to the first term in (5.5). Terms of lower degree in P cannot contribute at x^(q-2), by the moment cancellation already proved in Section 2. The P,b cross terms contribute the other two displayed terms. The b,b product has degree zero and cannot contribute, since q-2>=4.

Every term in (5.5) is positive. Indeed, `C>=binom(2d,2)=d(2d-1)` and d>=3 imply m=1+C/2>2d. Thus the first term is positive. Also c<0 and B_0<0. Finally m+1>2d+1 and d>=3 give `(2d-1)(m+1)>6d`, so B_2>0. Therefore beta>0. The actual leading degree on this residue is q-2, and translation back to n preserves its positive leading coefficient. Formula (3.1) supplies the required explicit bound. This completes the critical case and the classification. End of proof.

### Small order and strictness

The classification above deliberately states d>=2. At d=1,m=2, p_(1,2)(n)=floor((n+2)^2/4); the order-one transform is identically zero for even n and positive for odd n. Thus it is eventually nonnegative but not eventually strictly positive. For d=1,m>=3, (4.8) gives a negative residue. These checks prevent a silent extension of the strict statement to d=1.

## 6. Relation to the research target and review checklist

The source problem is Gajdzica, The Turan and Laguerre inequalities for quasi-polynomial-like functions, Research in Number Theory 10 (2024), article 46, Problem 5.6 (official full text personally opened). Its Theorem 4.3 already provides the smooth coefficient in Section 2. Its Example 4.6 already treats d=2,m=300, so that example alone is not a new result. The candidate contribution here is the general periodic boundary term, the explicit sign certificate, and the full parameter classification including the odd critical case. Novelty remains subject to separate checking; no assertion of global literature completeness is part of this proof.

The actual statement is restricted to exact quasi-polynomials and to the specified partition family. It does not solve all possible versions of the source's broad question. The unrestricted little-o version would additionally require a supplied error modulus for an explicit threshold.

Checks requested of reviewers: signs and shifts in (2.1)/(4.7)/(4.8); the exact polynomial decomposition; the centered coefficient in (5.2); the Fourier moment signs; cancellations and degrees at the critical residue; strictness and d=1; validity and explicitness of the bound; and whether any step relies on unproved numerical evidence.
