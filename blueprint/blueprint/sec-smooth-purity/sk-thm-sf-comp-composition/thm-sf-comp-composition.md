+++
id = "thm-sf-comp-composition"
kind = "theorem"
title = "The composition law for $Rf_!$"
order = 1516
uses = ["cor-weil-pbc-geometric-fiber-finite", "def-compact-support-direct-image-detailed", "def-weil-compactifications-refinements", "lem-weil-derived-direct-image-composition", "prop-compactification-coherence-detailed", "prop-compactification-refinement", "thm-nagata-compactification", "thm-weil-pbc-finite-level-proetale"]
lean = ["AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp"]
+++
Let $f:X\to Y$ and $g:Y\to S$ be separated of finite type between finite-type
$k$-schemes. There is a canonical isomorphism

$$
\alpha_{g,f}:\ Rg_!Rf_!\ \xrightarrow{\ \sim\ }\ R(g\circ f)_!
$$

of functors $D^+(X,\Lambda)\to D^+(S,\Lambda)$ on étale-origin complexes,
where $Rf_!$ is the compact-support direct image of
[def-compact-support-direct-image-detailed],
independent of all compactification choices by [prop-compactification-coherence-detailed],
equal to the identity when $f$ or $g$ is an identity, and associative:
for a third $h:S\to T$ the two composites
$Rh_!Rg_!Rf_!\to R(hgf)_!$ agree.

## Proof

*Construction.* Compactify $g$ as $Y\xrightarrow{v}\overline Y \xrightarrow{\bar g}S$, and compactify $v\circ f$ as
$X\xrightarrow{a}\overline X\xrightarrow{p}\overline Y$, using
Nagata's theorem [thm-nagata-compactification]. Put $V=\overline X\times_{\overline Y}Y$,
with its open immersion $b:V\to\overline X$ and proper projection
$p_Y:V\to Y$. Since $p\circ a=v\circ f$, the morphism $a$ factors as
$a=b\circ c$ through an open immersion $c:X\to V$, so
$X\xrightarrow{c}V\xrightarrow{p_Y}Y$ is a compactification of $f$ and
$Rf_!=Rp_{Y*}c_!$ on that model. For every
étale-origin $N$ on $V$ the map

$$
v_!Rp_{Y*}N\ \longrightarrow\ Rp_*b_!N
$$

is an isomorphism: over $Y$ it is proper base change for the Cartesian square
defining $V$ ([thm-weil-pbc-finite-level-proetale]), and at a geometric point of
$\overline Y$ outside $Y$ both sides vanish, because the corresponding fibre of
$p$ misses $V$ ([cor-weil-pbc-geometric-fiber-finite]). Apply this to the extension by zero of a complex on $X$ and
then push by $R\bar g_*$: extension by zero along opens composes termwise and
proper derived direct image composes
([lem-weil-derived-direct-image-composition]), giving $\alpha_{g,f}$.

*Independence and associativity.* Any two choices are compared by
[prop-compactification-coherence-detailed], which also makes $\alpha_{g,f}$ natural. For
three morphisms choose, by
[def-weil-compactifications-refinements], [prop-compactification-refinement] (i), a single common refinement of all
the compactifications involved; the two composites then restrict to the same
identity over the source and use the same proper base-change maps on each
Cartesian rectangle, so their pasting identity together with the refinement
transitivity of [prop-compactification-coherence-detailed] gives associativity.

Uses: [cor-weil-pbc-geometric-fiber-finite], [def-compact-support-direct-image-detailed], [def-weil-compactifications-refinements], [lem-weil-derived-direct-image-composition], [prop-compactification-coherence-detailed], [prop-compactification-refinement], [thm-nagata-compactification], [thm-weil-pbc-finite-level-proetale]
