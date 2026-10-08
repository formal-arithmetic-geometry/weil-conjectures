+++
id = "lemma-nagata-finite-type-nil-ideal-nilpotent"
kind = "lemma"
title = "A finite type nil ideal sheaf is uniformly nilpotent"
order = 245
+++
**Status.** Bypassed by the formalized route: boundary separation is
`AlgebraicGeometry.separationBlowup` with
`AlgebraicGeometry.exists_admissibleBlowup_disjoint_closures`,
proved from Deligne's disjointness blow-up rather than from this
preparation.

Let $X$ be quasi-compact and let $\mathcal I$ be a finite type
quasi-coherent ideal with $V(\mathcal I)=X$. Then there exists $n>0$ with
$\mathcal I^n=0$.

## Proof

On an affine open, let $x_1,\ldots,x_r$ generate the ideal. Every $x_i$
lies in every prime and is nilpotent; choose $n_i>0$ with $x_i^{n_i}=0$.
Set $N=1+\sum_i(n_i-1)$. Every degree-$N$ monomial in the generators
contains some $x_i^{n_i}$, so the $N$th power of the ideal is zero. Choose
a finite affine cover of $X$ and then a common exponent for the finitely many chart
exponents. Equality of quasi-coherent ideals is local, so that exponent
annihilates $\mathcal I$ globally.
