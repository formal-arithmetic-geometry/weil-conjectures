## What changed

Restored lean/Sheaf/Paper/ProperIndConstructibleBoundedBelow.lean from its exact
coord/rework.tsv quarantine archive. Compilation exposed a missing local instance in
hypercohomology_zero: the finite-filtration argument uses IsZero as an ObjectProperty,
which must be closed under isomorphisms. Added the proved instance using IsZero.of_iso.
Removed the unused private import Mathlib.CategoryTheory.ObjectProperty.Extensions.

Both coefficient cases, every declaration signature and visibility, all public imports,
and the complete exact-couple/finite-filtration proof are preserved. The original archive
is retained. The existing DAG proof, proof_deps and Lean attachment still describe the
restored proof exactly; no node changes are needed. The unit route is unchanged.

Change record: coord/changes/M2-proper-bounded-below-restoration.md.
Consumer search included the two quarantined direct importers; their public theorem and
private-helper interfaces are unchanged and neither requires adaptation.

## Proved and sorry left

This is a zero-hole rework item, not a new hole closure. Holes closed: 0. Holes added: 0.
Sorry left: none. Split off: none.

Restored complete proofs:
- AlgebraicGeometry.ProEtale.proper_indConstructible_boundedBelow
- AlgebraicGeometry.ProEtale.proper_indConstructible_boundedBelow_padicAlgCl

Both realize det-proper-unbounded-window-bounded-below. Every private helper is also
proved. The missing-instance failure was reproduced before the repair; the repaired
module compiled successfully. Delivery recompiles the final version after import pruning.

## No longer needed

Removed private import Mathlib.CategoryTheory.ObjectProperty.Extensions: the proof uses
short-exact extension hypotheses explicitly, rather than its ObjectProperty instances.
No DAG nodes or project modules are pruned. Every existing stated proof dependency is
retained, including exact couples, truncation hypercohomology, the proper heart bound,
and ind-constructible closure under kernels, cokernels and extensions.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined restoration with zero sorry, as its rework row allows.
The old bad-import failure no longer reproduces: those dependencies are now available.
The current failure was the missing IsZero isomorphism-closure instance; it is repaired
locally without changing any public API or mathematical statement. No mathematical
error in the DAG or the unit route was found. Mathlib searches found no replacement
for the existing spectral-sequence argument.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
