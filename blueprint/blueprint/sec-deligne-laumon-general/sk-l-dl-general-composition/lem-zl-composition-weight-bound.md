+++
id = "lem-zl-composition-weight-bound"
kind = "lemma"
title = "Composition preserves the direct-image weight bound"
order = 2821
lean = ["AlgebraicGeometry.HasDirectImageWeightBound.comp"]
uses = ["def-weil-pbc-hypercohomology-filtrations", "def-weil-pbc-qbar-category", "def-weil-punctual-weights", "lem-a1-mixed-direct-summand", "lem-zl-shriek-composition", "lemma-weil-pbc-hypercohomology-convergence"]
+++
Let $h:X_0\to Z_0$ and $g:Z_0\to Y_0$ be separated finite-type
morphisms of separated finite-type $k_0$-schemes. Suppose the
direct-image weight assertion holds for $h$ and for $g$: for every
real $v$, every $\iota$-mixed Weil sheaf of weights at most $v$ on the
source has its $i$th higher direct image with compact support
$\iota$-mixed of weights at most $v+i$, for every $i$. Then the same
assertion holds for $gh$: if $\mathcal F$ is an $\iota$-mixed Weil
sheaf on $X_0$ of weights at most $w$, then $R^n(gh)_!\mathcal F$ is
$\iota$-mixed of weights at most $w+n$ for every $n$.

## Proof

By [lem-zl-shriek-composition] there is a Frobenius-compatible
isomorphism $R(gh)_!\mathcal F\simeq Rg_!(Rh_!\mathcal F)$. Apply the
hypercohomology spectral sequence of the truncation construction
[def-weil-pbc-hypercohomology-filtrations] to the exact functor $Rg_!$
and the bounded complex $K=Rh_!\mathcal F$, whose cohomology sheaves
are $\mathcal H^b(K)=R^bh_!\mathcal F$. This is the compact-support
Leray spectral sequence

$$
E_2^{a,b}=R^ag_!\bigl(R^bh_!\mathcal F\bigr)
\ \Longrightarrow\ R^{a+b}(gh)_!\mathcal F,
$$

a spectral sequence of Weil sheaves (all maps are Frobenius-compatible,
[def-weil-pbc-qbar-category]), with only finitely many nonzero terms
and a finite abutment filtration
([lemma-weil-pbc-hypercohomology-convergence]).

By the assertion for $h$, the sheaf $R^bh_!\mathcal F$ is $\iota$-mixed
of weights at most $w+b$. By the assertion for $g$, applied with
$v=w+b$, the term $E_2^{a,b}$ is $\iota$-mixed of weights at most
$w+a+b$. Each later page $E_{r+1}^{a,b}$ is a subquotient of
$E_r^{a,b}$, so $E_\infty^{a,b}$ is a subquotient of $E_2^{a,b}$, and
the abutment $R^n(gh)_!\mathcal F$ carries a finite filtration whose
graded pieces are the $E_\infty^{a,b}$ with $a+b=n$; all of these are
constructible Weil sheaves and all maps are maps of Weil sheaves. For
$a+b=n$ the sheaf $E_2^{a,b}$ is $\iota$-mixed of weights at most
$w+n$, so by the sheaf-level stability of mixedness under Weil
subsheaves and quotients, [lem-a1-mixed-direct-summand](1), applied
page by page, so is $E_\infty^{a,b}$. Stability under extensions,
[lem-a1-mixed-direct-summand](2), applied along the finite filtration,
gives the same bound for $R^n(gh)_!\mathcal F$, in the sense of
[def-weil-punctual-weights].
