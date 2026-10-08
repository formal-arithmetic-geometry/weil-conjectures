+++
id = "lem-sc-p1-coherent-finite"
kind = "lemma"
title = "Finite coherent cohomology on the projective line"
order = 641
uses = ["def-sc-p1-standard", "lem-sc-cech-spectral", "pqf-def-coherent", "pqf-lem-affine-vanishing"]
+++
Let $k$ be a field and let $\mathcal F$ be a
coherent module on $\mathbf P^1_k$.
Then $H^0(\mathbf P^1_k,\mathcal F)$ and $H^1(\mathbf P^1_k,\mathcal F)$
are finite-dimensional over $k$.

## Proof

Use the standard affine opens $U_0,U_1$ of
[def-sc-p1-standard], namely
$U_0=\operatorname{Spec}k[t]$, $U_1=\operatorname{Spec}k[t^{-1}]$.
Put $M_i=\Gamma(U_i,\mathcal F)$ and
$M=\Gamma(U_0\cap U_1,\mathcal F)=M_0[t^{-1}]=M_1[t]$.
The Cech spectral sequence [lem-sc-cech-spectral] and affine
vanishing [pqf-lem-affine-vanishing] identify $H^0,H^1$ with
the kernel and cokernel of $M_0\oplus M_1\to M$.
Choose generators $a_j$ of $M_0$ over $k[t]$. Since $M=M_1[t]$,
some common $N$ has $t^{-N}a_j$ in the image of $M_1$ for every $j$.
Thus the cokernel is spanned by the finitely many $t^ra_j$ with
$-N<r<0$, proving finiteness of $H^1$.

For $H^0$, the localization kernels $K_i=\ker(M_i\to M)$ are killed
by powers of $t$ and $t^{-1}$ respectively, hence finite-dimensional.
Modulo the torsion submodule of the finite $R=k[t,t^{-1}]$-module $M$,
the elementary structure theorem gives a free module $R^r$; the torsion
is finite-dimensional over $k$. Images of finite generators of $M_0$
have a common lower Laurent exponent bound, and those of $M_1$ a common
upper bound. Their intersection therefore lies, modulo torsion, in a
finite-dimensional span of Laurent monomials between these bounds.
The exact sequence with kernel $K_0\oplus K_1$ now proves finiteness of
$H^0$.
