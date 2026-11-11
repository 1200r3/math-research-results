# Cayley equivalence through length five and for binary patterns of length six

A packed word has set of values [k]={1,...,k} for some k, with k=0 for the empty word. A word contains a packed pattern if an increasing sequence of positions induces the same strict order and equalities as the pattern. Write A_p(n,k) for the number of length-n packed words with value set [k] avoiding p, A_p(n)=sum_k A_p(n,k), and W_p(n,K) for the number of avoiding words over [K], whether or not all K letters occur.

Let p and q be nonempty packed patterns of the same length m. Assume either m<=5, or m=6 and each pattern uses at most two values. Then the following are equivalent:
1. A_p(n)=A_q(n) for every n>=0.
2. A_p(n,k)=A_q(n,k) for every n,k>=0.
3. W_p(n,K)=W_q(n,K) for every n,K>=0.

In this range, equality of A_p(n) and A_q(n) for n<=11 already implies these equivalent properties. This proves the indicated special case of Cerbai--Claesson--Ernst--Golab Conjecture 8.6 (2026, p.295), without a claim about other length-six patterns or arbitrary pattern length.