+++
id = "sk-cor-picard-pic-sheaf"
kind = "section"
title = "Picard functor is an fppf sheaf"
order = 808
uses = ["sk-def-picard-pic", "sk-thm-picard-descent"]
lean = ["AlgebraicGeometry.isSheaf_picardFunctorNormalized"]
+++
*Corollary (sketch).*

$\Pic_{X/S}$ is an fppf (hence Zariski) sheaf, being by
[sk-def-picard-pic] an fppf sheafification. If in addition $f$ has a
section $\sigma$ and $\cO_T\to f_{T,*}\cO_{X_T}$ is an isomorphism for
all $T\in\Ob((\Sch/S)_{fppf})$ — the hypotheses of
[sk-prop-picard-pic-split], satisfied for a smooth projective curve
over a field with a rational point — then
$\Pic_{X/S,\sigma}(T)=\ker\sigma_T^*$ is an fppf (hence Zariski) sheaf
as well. The presheaf $T\mapsto\Pic(X_T)$ itself is in general
*not* an fppf sheaf: [sk-thm-picard-descent] (D1) makes descent
data effective, but unnormalized glueing isomorphisms between the local
modules need not satisfy the cocycle condition. Repairing that is
exactly what the sheafification in [sk-def-picard-pic] and the
$\sigma$-normalization below do.

## Proof

The first assertion holds by construction. For the second, let
$\{T_i\to T\}_{i\in I}$ be an fppf covering and let
$\cL_i\in\Pic_{X/S,\sigma}(T_i)$ agree on the double intersections;
write $T_{ij}=T_i\times_TT_j$, $T_{ijk}=T_i\times_TT_j\times_TT_k$, and
choose trivializations $\alpha_i:\cO_{T_i}\to\sigma_{T_i}^*\cL_i$ and
isomorphisms
$\varphi_{ij}:\cL_i|_{X_{T_{ij}}}\to\cL_j|_{X_{T_{ij}}}$.

*Step 1 (normalize along the section).* The composite
$\alpha_j^{-1}\circ\sigma_{T_{ij}}^*\varphi_{ij}\circ\alpha_i$ is
multiplication by a unit $u_{ij}$ on $T_{ij}$; replacing
$\varphi_{ij}$ by $u_{ij}^{-1}\varphi_{ij}$ makes the $\varphi_{ij}$
compatible with the $\alpha_i$ along $\sigma$.

*Step 2 (the cocycle condition becomes automatic).* The self-map
$\varphi_{ki}\circ\varphi_{jk}\circ\varphi_{ij}$ of
$\cL_i|_{X_{T_{ijk}}}$ is multiplication by a unit
$u_{ijk}\in\Gamma(X_{T_{ijk}},\cO^*)$. The hypothesis
$\cO_T\overset{\sim}{\to}f_{T,*}\cO_{X_T}$ identifies
$\Gamma(X_{T_{ijk}},\cO^*)=\Gamma(T_{ijk},\cO^*)$, with $\sigma^*$
inverse to $f^*$; by Step 1 $\sigma^*u_{ijk}=1$, hence $u_{ijk}=1$.
This is the only place the section and the $H^0$ hypothesis are used,
and it is precisely what fails for the bare presheaf
$T\mapsto\Pic(X_T)$.

*Step 3 (descend).* So $\{\cL_i,\varphi_{ij}\}$ is a descent datum
for invertible modules on the fpqc covering $\{X_{T_i}\to X_T\}$, and
[sk-thm-picard-descent] (D1) yields an invertible $\cL$ on $X_T$ with
$\cL|_{X_{T_i}}\cong\cL_i$ compatibly with the $\varphi_{ij}$. The
$\alpha_i$ are then compatible as well, so they descend to a
trivialization of $\sigma_T^*\cL$: hence $\sigma_T^*\cL\cong\cO_T$ and
$\cL\in\Pic_{X/S,\sigma}(T)$. Uniqueness of glueing gives the
injectivity half of the sheaf condition.

This is the proof of Stacks, Picard Schemes of Curves, Lemma 44.4.3
([`0B9N`](https://stacks.math.columbia.edu/tag/0B9N)); the detailed forms are Blueprint 50,
`lem-pc-k-sheaf` and `lem-pc-fpqc-descent` (Descent,
Proposition 35.5.2, [`023T`](https://stacks.math.columbia.edu/tag/023T)).

Uses: [sk-def-picard-pic], [sk-thm-picard-descent]
