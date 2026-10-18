## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleUnitsPresheaf_isSheaf` in
`Sheaf.AlgebraicGeometry.ProEtaleUnitsSheaf` by applying Mathlib's
`CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf` to the structure sheaf and the exact
composite of forgetful, units, additive-transport and universe-lift functors used in the
presheaf definition. This follows the node's existing `mathlib_match`; the route and
all declaration signatures, definitions and existing public imports are unchanged.

Added the proof-only import
`WeilConjectures.Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup`, which registers
the existing additive-transport functor as an equivalence. Its limit preservation,
and those of the other three functors, are then inferred. The import-direction check
passes. The final module compiles through `lcompile.py` without errors or warnings
(4.4 seconds). No restrictions on the scheme were introduced; empty schemes and
zero section rings are covered by the same categorical result.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.proEtaleUnitsPresheaf_isSheaf`
(node `def-pur-proetale-units-sheaf`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
The proof uses the supplied structure sheaf, whose existing descent theorem
`AlgebraicGeometry.Scheme.proEtaleStructurePresheaf_isSheaf` remains a separate
upstream obligation in `Sheaf.AlgebraicGeometry.ProEtaleStructureSheaf`; this delivery
does not claim to close it.

## No longer needed

None: no original imports, declared dependencies, nodes or modules are pruned.
All four original public imports provide data used by the existing definitions.
No explicit inverse-gluing auxiliary lemmas are needed: the existing Mathlib
postcomposition theorem supplies that argument. A trial ring-adjunction import
was removed after compilation confirmed it was unnecessary; it is absent from
the final delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The node's existing Mathlib match correctly
identifies the short proof route. One instance must be made available explicitly:
Mathlib defines `commGroupAddCommGroupEquivalence` but does not register
`CommGrpCat.toAddCommGrp` itself as an equivalence. The existing project helper
supplies precisely this instance, without introducing any proof obligation.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
