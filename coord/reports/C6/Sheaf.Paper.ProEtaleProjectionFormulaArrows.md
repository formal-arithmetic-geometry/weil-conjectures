## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleProjectionUnit_existsUnique` in
`Sheaf.Paper.ProEtaleProjectionFormulaArrows`, preserving its statement and every
existing definition. The proof transports Mathlib's canonical unit isomorphism along
uniqueness of left adjoints, checks tensor compatibility through the adjunction on
pure tensors, and proves uniqueness by cancelling the tensor comparison and unitors.
Three proved private helpers supply tensor naturality, the right-unitor formula,
and extensionality on pure tensors. Explicitly typed sections avoid a rewrite failure
from unfolding sectionwise direct image.

Added the proof-only import
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree`. A section-local
irreducibility attribute keeps `proEtaleRingModuleAdjunction` abstract during this
proof; the attribute ends before the remaining declarations. The change record is
`coord/changes/C6-proetale-projection-unit-local-transparency.md`.

Validation: the complete candidate compiled through `lcompile.py` in 48.6 seconds,
with exit code zero and no diagnostics. Delivery preflight supplies the axiom check.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Scheme.proEtaleProjectionUnit_existsUnique`
(blueprint: `def-weil-pbc-projection-formula-arrows`). Added zero holes and split off
zero statements. Zero `sorry` remains in the item module. Existing proofs of
`proEtaleStrictPerfect_flat` and `proEtaleMixedTensor_existsUnique`, and the
mixed-tensor and projection-inverse constructions, are unchanged.

The proof uses the already stated canonical ordinary tensor-pullback comparison;
its upstream holes are existing dependencies, not new statements.

## No longer needed

No imports removed; no nodes or modules pruned. Existing imports support the
unchanged representative and finite-total inverse constructions. The new proof
uses the existing canonical tensor comparison and Mathlib's pullback-unit API.

## Where the brief, the DAG or earlier work was wrong

No statement correction or definition repair was needed. The attached definition
node has no numbered proof steps; the missing unit normalization follows from the
existing ordinary tensor comparison's pure-tensor characterization and Mathlib's
unit isomorphism for a final continuous functor. The retained first candidate had a
rewrite-transparency error; explicitly typing the sections repairs it without
changing an interface or any dependency.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
