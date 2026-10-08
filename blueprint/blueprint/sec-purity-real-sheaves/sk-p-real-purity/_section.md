+++
id = "sk-p-real-purity"
kind = "section"
title = "Purity of real lisse sheaves on curves"
order = 2665
uses = ["sk-d-real-detweights", "sk-d-real-operations", "sk-d-real-setup", "sk-d-real-weights", "sk-d-real-weil", "sk-i-real-boundary", "sk-p-exterior", "sk-p-linear-spectra", "sk-p-real-rankin", "sk-p-real-rankone", "sk-p-real-semi", "sk-r-real-linear"]
lean = ["AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_isConstituent_of_isReal"]
+++
*Proposition (sketch).*

Let $C_0/\Fq$ be a smooth geometrically connected
curve and $\mathcal F$ an $\iota$-real
lisse Weil sheaf.
Every irreducible constituent $V$ of
$\mathcal F$ is punctually $\iota$-pure of weight
$\dw_\iota(V)$.

## Proof

There is nothing to show for $\mathcal F=0$.
By [sk-r-real-linear], its semisimplification $\mathcal S$ has the same local
polynomials and is real. Choose a nonempty affine open $U_0\subset C_0$.
By [sk-i-real-boundary], restriction preserves irreducibility. It preserves
determinants and their weights by [sk-p-real-rankone], [sk-d-real-detweights].

Work first on $U_0$, and fix a nonzero weight block $\mathcal S(\gamma)$.
Use $N=N_\gamma$ and $B=B_\gamma$ from [sk-d-real-detweights].
The sheaf $\mathcal E=\bigwedge^{N+1}\mathcal S$ is nonzero and real
by [sk-r-real-linear]. The exterior rule of [sk-p-exterior] bounds its
constituent determinant weights by $B+\gamma$: the largest sum of
$N+1$ rank-counted entries takes every entry above $\gamma$ and one
entry equal to $\gamma$.

At a point of degree $e$, multiply a chosen eigenvalue $\alpha$ in
the $\gamma$-block by all eigenvalues of all higher blocks, with
multiplicity. The resulting $\delta$ occurs on $\mathcal E$ by
[sk-p-linear-spectra]. The determinants of the higher blocks have modulus
$q^{eB/2}$ by [sk-p-real-rankone], [sk-d-real-detweights]. Therefore [sk-p-real-rankin]
gives

$$
|\iota\alpha|q^{eB/2}=|\iota\delta|
\le q^{e(B+\gamma)/2},\qquad
|\iota\alpha|\le q^{e\gamma/2}.
$$

The individual block need not be real: the real object used here is
the exterior power of the whole $\mathcal S$.

If $\alpha_1,\ldots,\alpha_r$ are the eigenvalues of that block, then

$$
0<\frac{|\iota\alpha_i|}{q^{e\gamma/2}}\le1,\qquad
\prod_{i=1}^r\frac{|\iota\alpha_i|}{q^{e\gamma/2}}=1
$$

by its pure determinant, again using [sk-p-real-rankone].
Every factor must be $1$. This is purity on $U_0$ in [sk-d-real-weights],
for each constituent separately. Each constituent is lisse on $C_0$,
so [sk-p-real-semi] extends that purity over the missing points.

Uses: [sk-d-real-detweights], [sk-d-real-operations], [sk-d-real-setup], [sk-d-real-weights], [sk-d-real-weil], [sk-i-real-boundary], [sk-p-exterior], [sk-p-linear-spectra], [sk-p-real-rankin], [sk-p-real-rankone], [sk-p-real-semi], [sk-r-real-linear]
