+++
id = "pqf-lem-pushforward-qcoh"
kind = "lemma"
title = "Pushforward of quasi-coherent modules"
order = 542
uses = ["def-weil-pbc-scheme-conventions", "pqf-def-coherent", "pqf-lem-associated-sections-localize"]
+++
Let $f:X\to S$ be a quasi-compact and quasi-separated morphism of
schemes. Then $f_*$ transforms quasi-coherent $\mathcal O_X$-modules
into quasi-coherent $\mathcal O_S$-modules.
(*Stacks Project, Schemes, Lemma 26.24.1, Tag
[01LC](https://stacks.math.columbia.edu/tag/01LC).*)

## Proof

Work over an affine open $S_0=\operatorname{Spec}A\subset S$ and put
$X_0=f^{-1}(S_0)$. By quasi-compactness in
[def-weil-pbc-scheme-conventions], choose finitely many affine
opens $U_i=\operatorname{Spec}B_i$ covering $X_0$, small enough that
$\mathcal F|_{U_i}=\widetilde{M_i}$ as in
[pqf-def-coherent]. For each pair $i,j$, the intersection
$U_i\cap U_j$ is quasi-compact: it is the inverse image of the affine
$U_i\times_{S_0}U_j$ under the quasi-compact diagonal of $f$.
Choose a finite affine cover $W_{ijk}=\operatorname{Spec}C_{ijk}$
of this intersection, again with
$\mathcal F|_{W_{ijk}}=\widetilde{N_{ijk}}$.

The sheaf gluing axiom gives an exact sequence at its first two terms

$$
0\longrightarrow\Gamma(X_0,\mathcal F)
\longrightarrow\prod_i M_i
\xrightarrow{\delta}\prod_{i,j,k}N_{ijk},
$$

where $\delta$ is the difference of the two restrictions.
Indeed, a tuple of sections on the $U_i$ glues precisely when its
restrictions agree on every member $W_{ijk}$ covering every overlap.

For $a\in A$, pull these two finite covers back to $D(a)$. The same
gluing axiom computes $\Gamma(f^{-1}(D(a)),\mathcal F)$ as the kernel
of the resulting restriction-difference map. By
[pqf-lem-associated-sections-localize], its two terms and its
map are obtained from the displayed sequence by $-\otimes_AA_a$.
Localization is exact and commutes with finite products, hence

$$
\Gamma(f^{-1}(D(a)),\mathcal F)
\cong\Gamma(X_0,\mathcal F)\otimes_AA_a.
$$

These isomorphisms commute with further principal localization,
since every map used is restriction of sections. Thus on the basis
of principal opens of $S_0$, the sheaf $f_*\mathcal F$ agrees with
$\widetilde{\Gamma(X_0,\mathcal F)}$. It is quasi-coherent on $S_0$
by [pqf-def-coherent]; varying $S_0$ proves the assertion.
