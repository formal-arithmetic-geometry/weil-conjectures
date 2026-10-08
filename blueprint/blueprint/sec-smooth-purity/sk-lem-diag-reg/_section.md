+++
id = "sk-lem-diag-reg"
kind = "section"
title = "The diagonal is a regular immersion"
order = 2003
uses = ["sk-def-purity-conv"]
lean = ["AlgebraicGeometry.isRegularImmersion_diagonal"]
+++
*Lemma (sketch).*

Let $f:X\to Y$ be smooth, separated, of pure relative dimension $d$, put
$W=X\times_YX$ with projections $p_1,p_2$ and diagonal
$\Delta:X\hookrightarrow W$. Then $\Delta$ is a regular closed immersion of
pure codimension $d$, and its normal bundle is canonically
$N_{\Delta/W}\cong T_{X/Y}$, the relative tangent bundle of $f$.

## Proof

By the étale-local normal form, $f$ is étale-locally the projection
$\Aaf^d_Y\to Y$; on that model $\Delta$ is the zero section of $\Aaf^d$, a
regular closed immersion of codimension $d$ whose normal bundle is the
trivial rank-$d$ bundle, which the identification carries to $T_{X/Y}$.
Regular immersions, their codimension and their normal bundles are étale
local and compatible with étale base change, so the assertion follows.

Uses: [sk-def-purity-conv]
