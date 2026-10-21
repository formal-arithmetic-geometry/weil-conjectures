## What changed

Restored `lean/Sheaf/SixFunctors/BrownHypothesesAmbient.lean` from the exact
quarantine path in its current rework row. The archived theorem
`AlgebraicGeometry.ProEtale.det_brown_hypotheses_ambient` already has a complete
proof. All original hypotheses, conclusions, public imports and proof terms
are preserved. Removed one redundant private proof import, described below.
Updated only `proof_origin` in the existing node to record this restoration;
its Lean attachment, proof steps and dependency lists stay intact.
Change record: `coord/changes/H4-brown-ambient-quarantine-restoration.md`.

The proof applies the internal-module Grothendieck theorem to the actual pulled-back
coefficient ring, obtains local smallness and coproducts in its derived category,
checks zero, shift, triangle, isomorphism and coproduct closure by the defining
intersection, transfers local smallness by the faithful inclusion, and applies
the countable-coproduct idempotent-completeness theorem. The ULift equivalence
retains the specified u+1-small coproducts despite the larger indexing universe
of the original closure. This preserves the Brown-hypotheses unit route.

Validation: the restored archive compiles through lcompile.py in 4.7 seconds;
after the private import removal it compiles in 5.1 seconds, with no warnings.
The direct consumer and its four importers were inspected in quarantine; no
consumer adaptation is required. Search found triangulated-subcategory
infrastructure, but no shorter theorem for the exact intersection definition.
The empty family is included in the closure argument; the zero scheme, zero
coefficient ring, and zero/identity idempotents require no extra assumptions.

## Proved and sorry left

This is a quarantine restoration with zero original holes and zero remaining holes.
`AlgebraicGeometry.ProEtale.det_brown_hypotheses_ambient`
(node `det-brown-hypotheses-ambient`) retains its complete archived proof.
Holes closed: none. Holes added: none. Split off: none. No other declarations
are added. No new proof achievement is claimed for restoring this earlier proof.

## No longer needed

Removed the direct private import
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory` because
`Sheaf.CategoryTheory.GrothendieckDerivedCoproducts` already publicly imports it.
Its results are still used; this does not prune that module or its nodes from
the mathematical dependencies. No node or module is withdrawn or pruned.
All existing proof dependencies are retained, including those supplied by instances.

## Where the brief, the DAG or earlier work was wrong

The assignment is a rework restoration, rather than an unproved theorem: its
source is absent from lean/ and is preserved with a complete proof in quarantine.
The current rework row attributes the revert to cluster restoration. The archived
proof compiles against the current published library without any proof repair.
The older docstring describes a longer sectionwise ring-sheaf route; the actual
proof and current DAG already use the shorter internal-module Grothendieck theorem.
No mathematical statement, definition or target has been changed.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
