+++
id = "sk-lem-sf-twist-interchange"
kind = "section"
title = "Internal Hom with an invertible twist"
order = 2175
uses = ["sk-lem-sf-determination", "sk-prop-sf-dualizable-biduality"]
lean = ["AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_derivedHom_tensor"]
+++
*Lemma (sketch).*

Let $K$ be perfect over $\Lambda_X$, $M\in\Dctf(X,\Lambda)$ and $m\in\Z$. Then
$\Lambda(m)_X$ is invertible locally constant of rank one and the canonical map

$$
\RHom_X\bigl(K,M\otimes^L_{\Lambda_X}\Lambda(m)_X\bigr)\to
\RHom_X(K,M)\otimes^L_{\Lambda_X}\Lambda(m)_X
$$

is an isomorphism; in particular
$\RHom_X(K,\Lambda_X(m)[n])\cong K^\vee(m)[n]$.

## Proof

By def:coefficient-twists each $\Lambda(m)_X$ is invertible locally
constant of rank one with $\Lambda(m)\otimes^L\Lambda(-m)\cong\Lambda_X$, so
$T_m=-\otimes^L\Lambda(m)_X$ is an exact autoequivalence with inverse
$T_{-m}$. For an invertible $N$ the canonical map
$c_{M,N}:\RHom_X(K,M)\otimes^LN\to\RHom_X(K,M\otimes^LN)$ (adjoint to
$\mathrm{ev}\otimes1$) is an isomorphism: by the coherence of these maps,
$c_{M\otimes N,N^{-1}}\circ(c_{M,N}\otimes N^{-1})=c_{M,N\otimes N^{-1}}$ is
the identity under $N\otimes N^{-1}\cong\Lambda_X$, and symmetrically on the
other side, so $c_{M,N}$ has a two-sided inverse. (No appeal to a generator
is made: $\Lambda_X$ does not generate $\Dctf$, and [sk-lem-sf-determination]
propagates invertibility only.) For perfect $K$ the map is the
identification of [sk-prop-sf-dualizable-biduality] twisted by the invertible
local system, computed locally on a bounded complex of finite projectives.

Uses: `\Cref{sk-prop-sf-dualizable-biduality}`, `def-coefficient-twists-detailed`, [sk-lem-sf-determination]
