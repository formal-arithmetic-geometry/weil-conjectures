+++
id = "sk-lem-nagata-sketch-near-closure"
kind = "section"
title = "Isomorphism near a boundary closure"
order = 255
uses = ["sk-lem-nagata-sketch-boundary", "sk-lem-nagata-sketch-elimination"]
lean = ["AlgebraicGeometry.exists_admissibleBlowup_isIso_strictTransformMap_near_closure"]
+++
*Lemma (sketch).*

Let $q:Z\to X$ be proper with $X$ qcqs, let $V\subseteq X$ be
quasi-compact open, and let $T\subseteq V$ be closed. If $q$ is an
isomorphism over a neighbourhood of $T$ in $V$, a $V$-admissible
blow-up makes its strict transform an isomorphism near the closure of
$T$ in the new ambient scheme; see 0F3W.

## Proof

Enlarge $T$ and the closed non-isomorphism locus in $V$ to disjoint
constructible closed subsets. Separate their closures by
[sk-lem-nagata-sketch-boundary]. Away from the second closure,
eliminate indeterminacy and extend this blow-up to $X$ while preserving
$V$. The resulting strict transform is a proper open immersion near
the first closure. Its image contains $T$, and being closed there it
contains its closure, giving the required isomorphism neighbourhood.

Uses: [sk-lem-nagata-sketch-boundary], [sk-lem-nagata-sketch-elimination]
