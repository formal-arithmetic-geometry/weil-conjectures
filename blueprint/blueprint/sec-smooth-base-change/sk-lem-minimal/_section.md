+++
id = "sk-lem-minimal"
kind = "section"
title = "Minimal counterexamples occur over a point"
order = 1385
uses = ["sk-def-bc"]
lean = ["AlgebraicGeometry.Scheme.IsQcqsLocalProperty", "AlgebraicGeometry.exists_spec_field_of_isQcqsLocalProperty"]
+++
*Lemma (sketch).*

(Stacks Project, Lemma 59.88.5, Tag `0F06`.) Let $T$ be
quasi-compact quasi-separated and let $P$ be a property of qcqs
schemes over $T$ such that: (1) $P$ is invariant under thickenings;
(2) $P$ is compatible with limits with affine transition morphisms;
(3) if $Z\subseteq T'$ is closed with quasi-compact complement $V$
and $P(T')$ holds, then $P(V)$ or $P(Z)$ holds; (4) $P$ does not
hold for the empty scheme. Then $P(T)$
implies $P(\Spec K)$ for some morphism $\Spec K\to T$ with $K$ a
field.

## Proof

Zorn's lemma on the closed subschemes of $T$ satisfying $P$ (chains
have lower bounds by (2), the transition maps being closed
immersions) gives a minimal $T'$; it is nonempty by (4) and reduced
(by (1)). Let $\eta=\Spec K$ be the generic point of an irreducible
component of $T'$; it is the limit of its affine open
neighbourhoods $V$, and each such $V$ has $P$: otherwise (3) gives
$P(T'\setminus V)$, a strictly smaller closed subscheme as
$\eta\in V$, against minimality. Then (2) gives $P(\eta)$.

Uses: [sk-def-bc]
