## What changed

Proved `AlgebraicGeometry.normalGeometricCoverComponents` by the existing five-step
DAG argument. Constructed the component family directly from the fibres of
`ConnectedComponents.mk`, using `normal_etale_components_clopen` for openness.
Applied `geometricCoverComponentQcProper` and the proper-with-finite-fibres
characterization of finiteness. The nonempty clopen image of each restricted
étale proper map gives surjectivity. Mathlib's disjoint-open coproduct criterion
finishes the decomposition, including an empty source or an infinite component
index. No signatures, visibility, docstrings or imports changed.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.normalGeometricCoverComponents`
(node `lem-a1-normal-geometric-cover-components`). Added zero holes; zero explicit
holes remain in the item module. The proof uses the existing, separately stated
component lemmas; their proofs remain separate items. This is a proof from the
stated dependencies, with no new intermediate statements.

The repaired module compiled cleanly through `lcompile.py` (exit code 0, 26.0 s),
without warnings. Delivery preflight also probes the declaration for direct holes
and axioms.

## No longer needed

None. Every original proof dependency is used, and no import was removed.
No node or module is pruned; the proof follows the existing five-step plan.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. Mathlib already provides the disjoint-open
coproduct criterion for the elementary final step, so no new node is needed.

The retained draft was unvalidated because the preceding session received three
compile-server failures. This session's initial dry run also received no answer
within 184 seconds; a direct compile retry failed after 206 seconds. A further
dry run reached Lean and diagnosed an ambiguous `IsConnected` and four `haveI`
style warnings. Qualified the topology predicate and used `have` for the local
instances. The subsequent clean compile validates the repaired draft.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
