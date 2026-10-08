+++
id = "sk-lem-nagata-sketch-dense-valuative"
kind = "section"
title = "Dense-source valuative criterion"
order = 273
lean = ["AlgebraicGeometry.UniversallyClosed.of_valuativeCriterion_of_isDominant", "AlgebraicGeometry.IsSeparated.of_valuativeCriterion_of_isDominant"]
+++
*Lemma (sketch).*

Let $W\to S$ be separated and of finite type and let $D\subseteq W$
be a dense quasi-compact open. If every valuation diagram over $S$
whose generic point maps into $D$ extends to $W$, then $W\to S$
is proper; see 0894.

## Proof

The dense-source valuative criterion tests universal closedness using
valuation rings with generic map in $D$. Its reduction to these probes
uses quasi-compactness, specialization to the dense source, and extension
of valuation rings along field extensions. Uniqueness follows from
separatedness; universal closedness together with finite type and
separatedness gives properness.
