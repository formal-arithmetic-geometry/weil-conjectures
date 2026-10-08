+++
id = "sk-prop-deg0"
kind = "section"
title = "Degree-zero flat base change"
order = 1381
uses = ["sk-def-bc"]
lean = ["AlgebraicGeometry.Etale.baseChangeProperty_zero", "AlgebraicGeometry.Etale.baseChangeProperty_zero_of_smooth"]
+++
*Proposition (sketch).*

For a Cartesian square as in [sk-def-bc] in which $f:X\to S$ is flat
and locally of finite presentation with geometrically reduced fibres (in
particular for $f$ smooth), the degree-zero base-change map

$$
f^{-1}g_*\mathcal F\longrightarrow h_*e^{-1}\mathcal F
$$

is an isomorphism, for *every* sheaf $\mathcal F$ on $T_{\Et}$ — no
torsion hypothesis is needed in degree zero. Hence
$\mathrm{BC}(f,n,0)$ holds for smooth $f$.

## Proof

*Step 1 (an étale-local normal form with connected fibres).*
Because $f$ is flat, locally of finite presentation and has
geometrically reduced fibres, there is an étale covering
$\{X_i\to X\}$ such that each $X_i\to S$ factors as
$X_i\to S_i\to S$ with $S_i\to S$ étale and $X_i\to S_i$ flat of
finite presentation with geometrically connected (and geometrically
reduced) fibres. Geometric reducedness is what allows a geometric
fibre to be cut into quasi-compact geometrically connected opens which
then spread out over an étale neighbourhood of the base point.

*Step 2 (sections agree on such a chart).* Let $U\to X$ be étale
and factor as $U\to V\to S$ with $V\to S$ étale and $U\to V$
quasi-compact flat with geometrically connected fibres. Since $V\to S$
is étale, the inverse image of a sheaf on $S_{\Et}$ restricted to $V$
is its restriction, so

$$
(f^{-1}g_*\mathcal F)(U)=(g_*\mathcal F)(V)
=\mathcal F(V\times_ST)=(e^{-1}\mathcal F)(U\times_XY)
=(h_*e^{-1}\mathcal F)(U).
$$

The outer two equalities are the definitions of $g_*$ and $h_*$ together
with $U\times_XY=U\times_ST$. The first and third use the same input:
for a flat quasi-compact morphism with geometrically connected fibres,
global sections of an inverse image agree with global sections
downstairs ([Stacks `0A3H`](https://stacks.math.columbia.edu/tag/0A3H)) — applied to $U\to V$,
and then to its base change $U\times_ST\to V\times_ST$, whose fibres are
base changes of those of $U\to V$ and hence still geometrically
connected. That lemma is itself the statement that a section of the
pullback is constant on each connected geometric fibre, so descends
along the fpqc covering $U\to V$.

*Step 3 (glue).* Both sides are sheaves on $X_{\Et}$, and by
Step 1 every object of $X_{\Et}$ has a covering by objects of the shape
used in Step 2, so the two sheaves agree.

*Step 4 ($\mathrm{BC}(f,n,0)$ for smooth $f$).* A smooth morphism
is flat and locally of finite presentation and its geometric fibres are
smooth varieties, hence reduced; so Steps 1–3 apply and give the
degree-zero case of [sk-def-bc] for every quasi-compact
quasi-separated $g:T\to S$ and every $\Z/n\Z$-sheaf $\mathcal F$.

This is Stacks, Étale Cohomology, Lemma 59.87.2
([`0EYS`](https://stacks.math.columbia.edu/tag/0EYS)), combining Lemma 59.87.1
([`0EZX`](https://stacks.math.columbia.edu/tag/0EZX)) for Steps 2–3 with More on Morphisms,
Lemma 37.46.3 ([`0EY5`](https://stacks.math.columbia.edu/tag/0EY5)) for Step 1; the detailed
form is Blueprint 07,
`sbc-lem-degree-zero-flat-base-change`. (The statement above is
written in the letters of [sk-def-bc].)

Uses: [sk-def-bc]
