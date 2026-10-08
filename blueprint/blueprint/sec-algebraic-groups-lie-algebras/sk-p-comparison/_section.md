+++
id = "sk-p-comparison"
kind = "section"
title = "Group–Lie comparison"
order = 2496
uses = ["sk-d-geometry", "sk-d-lie", "sk-d-tangent", "sk-i-cartier", "sk-p-geometry"]
lean = ["Matrix.GeneralLinearGroup.invariant_iff_differential_invariant", "Matrix.GeneralLinearGroup.lieAlgebra_identityComponent_center"]
+++
*Proposition (sketch).*

Let $G$ be a connected matrix algebraic group.
For a rational representation $r:G\to\GL(M)$,
a subspace $U\subseteq M$ is $G$-invariant if and only if it is
invariant under $dr(\Lie(G))$. Moreover,

$$
\Lie\bigl(Z(G)^\circ\bigr)=Z\bigl(\Lie(G)\bigr).
$$

## Proof

In a basis adapted to $U$, its stabilizer is defined by the vanishing
of the lower-left block of $r(g)$. The resulting subgroup scheme is
reduced by [sk-i-cartier], and differentiation of these equations,
as in [sk-d-tangent], identifies its tangent algebra with
$\{X:dr(X)U\subseteq U\}$. Lie-invariance therefore gives equality
of tangent spaces and dimensions. By [sk-p-geometry], the stabilizer
is all of $G$; the converse follows by differentiation.

Differentiating the center equations of [sk-d-geometry] identifies
$\Lie(Z(G))$ with the adjoint-fixed vectors; [sk-i-cartier] again
justifies using those equations without a change of tangent space.
Adjoint-fixed vectors lie in the Lie center of [sk-d-lie].
Conversely, for $x\in Z(\Lie(G))$, the line $k(x,1)$ in the rational
representation $\Lie(G)\oplus k$ is killed by its differential.
The subspace assertion just proved makes this line $G$-invariant;
its last coordinate forces $(\operatorname{Ad}(g)x,1)=(x,1)$.
Finally [sk-i-cartier] identifies the tangent spaces of $Z(G)$ and
$Z(G)^\circ$.

Uses: [sk-d-geometry], [sk-d-lie], [sk-d-tangent], [sk-i-cartier], [sk-p-geometry]
