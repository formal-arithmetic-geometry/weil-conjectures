## What changed

Proved `CategoryTheory.Sheaf.supportedSectionsFunctor_additive` in
`Sheaf.AlgebraicGeometry.SupportCohomology`. After constructing the additive-functor
instance, kernel extensionality reduces preservation of addition to the corresponding
identity on sections. Simplification uses pointwise addition of sheaf morphisms and
bilinearity of composition. The complete module compiled with lcompile.py (4.4 seconds).
All existing signatures, definitions, visibility, and imports are unchanged.

## Proved and sorry left

Closed 1 of 1 holes: `CategoryTheory.Sheaf.supportedSectionsFunctor_additive`
(node `def-pur-support-cohomology`). Added 0 holes; split off 0 statements.
There are no remaining `sorry` declarations in the delivered module.

## No longer needed

None. No imports were added or removed. The node has no declared proof dependencies;
the elementary kernel-extensionality argument in its Lean docstring suffices, using
Mathlib lemmas already available through the existing imports. No nodes or modules
are bypassed or made obsolete, and the unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

None. The existing docstring gives the proof used. The definition node has no numbered
proof steps to translate or update. LeanFinder returned related sheaf-additivity
instances, and Loogle returned the kernel-map construction; neither gave a replacement
for the supported-sections construction. The direct argument proves its additivity
without any additional project dependency.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
