## What changed

Only `lean/Sheaf/Paper/CompletedExtensionZeroComparison.lean` changes. All existing
public signatures, definitions, instances, attributes and public imports are preserved.

The ordinary-to-completed comparison is the composite of the existing natural
transformations, so its naturality follows directly. Open immersions are weakly
etale by the existing instances. Slice continuity follows from the concrete slice
equivalence and cocontinuity of its inverse; open-site continuity is the existing
pro-etale composition theorem.

The finite coefficient maps are the sheafification comparisons of the identical
function presheaves. The sheafification universal property proves their specified
uniqueness. Their naturality in quotient transitions supplies strict tower maps;
taking limits constructs the completed maps, whose uniqueness is detected by all
finite projections. The slice construction reuses the private argument found in
`RingedOpenStrictReduction`, which cannot be imported here because it imports this
module. Every added helper is private and fully proved.

Additivity and exactness use `localizedSystemExtension` at the actual independent
site universes. The coefficient transport preserves finite limits; its invertible
completed coefficient map makes it a left adjoint, giving finite colimits. The
underived inverse exchange is invertible because the specified right exchange is
sectionwise restriction along the Cartesian site comparison isomorphism, and
adjoint conjugation preserves isomorphisms.

The complete file compiled without diagnostics in 37.4 seconds before final
comment/import cleanup. The delivery tool checks the final file and its axioms.
No other existing module needs adaptation because no public interface changes.

## Proved and sorry left

Closed 12 of the original 19 holes; added 0 holes and split off 0 statements.
All names below have namespace `AlgebraicGeometry.Scheme`.

Proved:

- `cbcCompletedPullbackComparison_naturality`
- `cbcOpenWeaklyEtale`
- `cbcSliceFunctor_continuous`
- `cbcFiniteSliceMap_exists`
- `cbcCompletedSliceMap_exists`
- `cbcOpenShriek_additive`
- `cbcOpenShriek_finiteLimits`
- `cbcOpenShriek_finiteColimits`
- `cbcOpenSiteFunctor_continuous`
- `cbcFiniteRestrictionMap_exists`
- `cbcCompletedRestrictionMap_exists`
- `cbcUnderivedInverseExchange_isIso`

The underived isomorphism proof uses the existing, still-stated canonical
`cbcRightExchange_exists`; this is an existing proof dependency, not a new hole.

Seven original holes remain, unchanged, all tagged in their existing docstrings
with `lem-cbc-completed-extension-zero-comparison`:

- `cbcModulePullbackAdjunction_exists`
- `cbcOpenAdjunction_exists`
- `cbcRightExchange_exists`
- `cbcDerivedInverseExchange_exists`
- `cbcDerivedInverseExchange_isIso`
- `cbcCompletedExchange_exists`
- `completedExtensionZeroComparison`

The final completed comparison has not been proved or decomposed in this packet.

## No longer needed

Removed these private imports, which the current constructions do not use:

- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.ExactFunctorDerivedLimit`
- `WeilConjectures.Algebra.Homology.RoosComplex`
- `WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism`

No DAG node or library module is withdrawn. The final theorem remains open, so
its full finite-reduction/Koszul/Rlim proof plan and dependencies are retained.
The import removals do not assert that an unfinished parent's dependencies are
mathematically unnecessary.

## Where the brief, the DAG or earlier work was wrong

The conceptual node `lem-cbc-completed-extension-zero-comparison` now attaches to
`Sheaf.Paper.CompletedOpenExchangeTransport`, which retains this older API as a
prerequisite. No node's `lean.module` is the assigned legacy module. The present
proofs implement its existing coefficient and exactness constructions without
changing the conceptual node's route, statement or attachment.

Several declared downstream dependencies, notably `RingedOpenStrictReduction`,
already import the assigned module. Importing them here would create a cycle;
the private coefficient arguments above provide the needed constructions directly.
The new independent-universe localized extension import was checked by
`tools/import_direction.py may` and does not create a cycle.

The current blueprint unit was read from `literature/blueprint/latest`; the old
standalone completed-extension-zero lemma path recorded in the DAG is absent in
that snapshot. No statement or unit route was changed in response.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
