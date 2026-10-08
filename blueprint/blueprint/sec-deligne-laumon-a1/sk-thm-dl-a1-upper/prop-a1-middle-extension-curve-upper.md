+++
id = "prop-a1-middle-extension-curve-upper"
kind = "theorem"
title = "Upper bound for a curve middle extension"
order = 2808
tags = ["latex:proposition"]
uses = ["def-weil-ordinary-compact-cohomology", "def-weil-punctual-weights", "def-wf-middle-extension", "lem-a1-affine-core-of-curve", "lem-a1-extension-bounds", "lem-a1-finite-boundary-cohomology", "lem-a1-finite-boundary-weights", "lem-a1-lisse-middle-extension", "lem-a1-subquotient-extension-bounds", "lem-wf-boundary-semicontinuity", "lem-wf-boundary-stalk-invariants", "prop-a1-curve-boundary-sequence", "thm-a1-affine-curve-upper"]
+++
Let $j:U_0\hookrightarrow C_0$ be a dense open immersion of smooth
geometrically connected curves, and let $\mathcal F$ be lisse and
punctually $\iota$-pure of weight $w$ on $U_0$. Then

$$
H_c^r(C,j_*\mathcal F)\quad\text{has weights at most }w+r
$$

for every $r$, where $j_*\mathcal F$ is the
middle extension.

## Proof

Choose a dense affine $v:V_0\hookrightarrow U_0$ by
[lem-a1-affine-core-of-curve]. The recovery lemma
[lem-a1-lisse-middle-extension] identifies
$v_*\mathcal F|_V$ with $\mathcal F$, so by transitivity of ordinary
direct image, $j_*\mathcal F$ is the middle extension of
$\mathcal F|_{V_0}$ directly from $V_0$ to $C_0$.

The affine estimate [thm-a1-affine-curve-upper] bounds
$H_c^r(V,\mathcal F)$ by $w+r$. The boundary stalk at a point of
the finite complement $C\setminus V$ is the inertia invariants of the
local geometric generic stalk, of weights at most $w$ by the
weights-of-inertia-invariants corollary [lem-wf-boundary-semicontinuity]
(with the boundary stalk description of
[lem-wf-boundary-stalk-invariants]), and the finite-boundary
calculation [lem-a1-finite-boundary-cohomology] then shows that
the boundary term of
the localization triangle [prop-a1-curve-boundary-sequence] for
$V\hookrightarrow C$ is concentrated in degree zero, and
[lem-a1-finite-boundary-weights] gives its weights at
most $w$. Thus each middle cohomology group $H_c^r(C,j_*\mathcal F)$
is an extension of a quotient of $H_c^r(V,\mathcal F)$ by a subobject
of the (degree-zero) boundary group; when $r=0$ it is an injection.
Subquotients preserve the stated bounds by
[lem-a1-subquotient-extension-bounds], and extensions preserve
them by [lem-a1-extension-bounds]; since $r\geq0$, the boundary bound $w$ is at
most $w+r$.
