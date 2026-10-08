+++
id = "sk-thm-sf-comp-composition"
kind = "section"
title = "The composition law for $Rf_!$"
order = 1515
uses = ["sec-nagata-compactification", "sec-proper-base-change", "sk-prop-nagata-sketch-comp-category", "sk-prop-sf-comp-coherence", "sk-thm-properbasechange"]
lean = ["AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp"]
+++
*Theorem (sketch).*

Let $f:X\to Y$ and $g:Y\to S$ be separated of finite type between finite-type
$k$-schemes. There is a canonical isomorphism

$$
\alpha_{g,f}:\ Rg_!Rf_!\ \xrightarrow{\ \sim\ }\ R(g\circ f)_!
$$

of functors $D^+(X,\Lambda)\to D^+(S,\Lambda)$ on étale-origin complexes,
independent of all compactification choices by [sk-prop-sf-comp-coherence],
equal to the identity when $f$ or $g$ is an identity, and associative:
for a third $h:S\to T$ the two composites
$Rh_!Rg_!Rf_!\to R(hgf)_!$ agree.

## Proof

*Construction.* Compactify $g$ as $Y\xrightarrow{v}\overline Y \xrightarrow{\bar g}S$, and compactify $v\circ f$ as
$X\xrightarrow{a}\overline X\xrightarrow{p}\overline Y$, using
[sk-thm-nagata-compactification]. Put $V=\overline X\times_{\overline Y}Y$,
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
defining $V$ ([sk-thm-properbasechange]), and at a geometric point of
$\overline Y$ outside $Y$ both sides vanish, because the corresponding fibre of
$p$ misses $V$. Apply this to the extension by zero of a complex on $X$ and
then push by $R\bar g_*$: extension by zero along opens composes termwise and
proper derived direct image composes, giving $\alpha_{g,f}$.

*Independence and associativity.* Any two choices are compared by
[sk-prop-sf-comp-coherence], which also makes $\alpha_{g,f}$ natural. For
three morphisms choose, by
[sk-prop-nagata-sketch-comp-category] (i), a single common refinement of all
the compactifications involved; the two composites then restrict to the same
identity over the source and use the same proper base-change maps on each
Cartesian rectangle, so their pasting identity together with the refinement
transitivity of [sk-prop-sf-comp-coherence] gives associativity.

Uses: `\Cref{sk-prop-nagata-sketch-comp-category}`, `\Cref{sk-prop-sf-comp-coherence}`, `\Cref{sk-thm-properbasechange}`
