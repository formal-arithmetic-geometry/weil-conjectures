+++
id = "prop-exc-finite-etale-adjoint"
kind = "theorem"
title = "The right adjoint for a finite etale morphism"
order = 2062
tags = ["latex:proposition"]
uses = ["def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-finite-torsion-constructibility", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-fet-locally-trivial"]
+++
Let $A=A_{E,n}$ be a
finite coefficient ring,
and let $e:V\to X$ be
finite etale.
On the small pro-etale sites,
direct image is exact and

$$
Re_!=Re_*=e_*\dashv e^*
\quad\hbox{on }D(V_{\mathrm{proet}},A),D(X_{\mathrm{proet}},A).
$$

Here $e^*$ is the
inverse image.

## Proof

By [lem-fet-locally-trivial], there is an etale covering of $X$
over which $V$ is a finite disjoint union of copies of the base.
This is also a covering for [def-weil-pbc-proetale-site].
On such a member, write the sheets as $1,\ldots,r$. A sheaf on $V$
is a tuple $(M_1,\ldots,M_r)$; direct image and inverse image of
[def-weil-derived-direct-image], [def-weil-derived-pullback-tensor-hom]
are respectively

$$
(M_1,\ldots,M_r)\longmapsto\bigoplus_{s=1}^r M_s,
\qquad N\longmapsto(N,\ldots,N).
$$

Finite sums of modules are exact. Moreover,
$\operatorname{Hom}(\bigoplus_s M_s,N) =\prod_s\operatorname{Hom}(M_s,N)$.
These formulas commute with permutations of the sheets; therefore the
adjunction maps glue on overlaps. Both functors are exact, so their unit,
counit, and triangular identities descend from complexes to the ordinary
derived categories. Finally $e$ is proper, so its proper
compactification is itself and $Re_!=Re_*$.
