+++
id = "sk-lem-nagata-sketch-boundary"
kind = "section"
title = "Separating boundary closures"
order = 244
uses = ["sk-lem-nagata-sketch-blowups"]
lean = ["AlgebraicGeometry.exists_admissibleBlowup_disjoint_closures"]
+++
*Lemma (sketch).*

If $V\subseteq X$ is quasi-compact open in a qcqs scheme and
$T_1,T_2$ are disjoint constructible closed subsets of $V$, a
$V$-admissible blow-up makes their closures disjoint.

## Proof

Represent the two subsets by finite-type ideals on $V$, extend the
ideals to $X$, and apply the closed-boundary separation blow-up.
The strict-transform chart calculation separates their closures.
Disjointness persists under any further blow-up preserving $V$.

Uses: [sk-lem-nagata-sketch-blowups]
