## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleSliceModuleRestriction_exact` in
`Sheaf.AlgebraicGeometry.ProEtaleCoefficientSliceClosedComparison`.
Presheaf restriction preserves finite limits, and the forgetful functor reflects them.
The composition/base-change adjunction and cocontinuity make this module restriction
a left adjoint, so it preserves finite colimits. Additivity holds on sections.
No signatures, definitions, imports, or other modules changed.

## Proved and sorry left

Closed one of the item's two holes:
`AlgebraicGeometry.Scheme.proEtaleSliceModuleRestriction_exact`.
Added zero holes and split off zero statements.

The remaining original hole is
`AlgebraicGeometry.Scheme.proEtaleCoefficientSliceClosedComparison`
(node `lem-zl-proetale-coefficient-slice-closed-comparison`). Its statement and
whole-proof `sorry` are unchanged. This delivery is a partial proof, not a proof
of the main closed comparison theorem.

## No longer needed

None. No imports, nodes, or modules are pruned. The main comparison remains open,
so its planned dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical error established. The stage-2 review noted that the exactness
assertion duplicates the proved `proEtaleSliceModules_exact` in
`Sheaf.AlgebraicGeometry.ProEtaleScalarExtensionSliceComparison`. That module also
imports bounded-constructible tower theory. The present proof uses the same direct
Mathlib argument without adding that proof import or changing either definition.

The main theorem requires transporting the normalized generic slice tensor/Hom
interfaces from `Over U` to `U.left.ProEt`, together with scalar transport and the
canonical pullback comparison. The existing generic slice theorem does not have
these concrete endpoints directly; no replacement claim or extra hole is introduced.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
