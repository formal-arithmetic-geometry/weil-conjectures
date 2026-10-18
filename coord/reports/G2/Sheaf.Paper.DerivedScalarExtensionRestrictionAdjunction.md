## What changed

Repaired `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction` by removing the two
private helper theorems whose statements duplicated `pro_absolute` and `pro_preserves_at`
from `Sheaf.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility`. The proof now
imports and applies that existing compatibility theorem. The remaining proof constructs the
filtered essential-constancy witness for exact restriction and derives the required unit
formula by naturality and the factorization isomorphism.

The three original theorem statements are unchanged. The existing proof-valued definition
`scalarReductionDerivedExistence` has an explicit canonical type, as recorded below; no new
public declarations or definitions were added.

For reviewer C-26de8, H9, removed the four unused imports named in the return. Kept
`Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived` and
`WeilConjectures.Mathlib.Algebra.Homology.Localization`, which the proof needs.
The existing interface change is recorded in
`coord/changes/scalar-reduction-derived-witness-interface.md`.

## Proved and sorry left

All three original holes are closed:

- `WeilConjectures.scalarReductionRestriction_exact`;
- `WeilConjectures.scalarReductionExtension_adjunction`;
- `WeilConjectures.derivedScalarExtensionRestrictionAdjunction`.

Holes added: zero. Holes left: zero.

## No longer needed

The local duplicate helpers `ScalarReductionDerivedProof.pro_absolute` and
`ScalarReductionDerivedProof.pro_preserves_at` are no longer present or used. The proof
does not need any additional theorem beyond the existing compatibility module and the
eventually-constant cocone construction used by the exact restriction argument. No DAG
node or module is withdrawn.

Unused imports removed for H9:

- `Mathlib.CategoryTheory.Functor.Derived.Adjunction`;
- `Mathlib.CategoryTheory.Functor.KanExtension.Preserves`;
- `Mathlib.Algebra.Homology.DerivedCategory.Fractions`;
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge`.

The old-route imports from the library version are also unnecessary:

- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`;
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`;
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`;
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`;
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`;
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars`.

The same-site tensor construction, resolving-class argument and existing derived-adjunction
compatibility theorem supply the proof instead.

## Where the brief, the DAG or earlier work was wrong

The returned delivery restated two theorems already present word for word in
`Sheaf.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility`; the import-prune
review correctly rejected that duplication. This repair uses the existing public
compatibility theorem and leaves all target statements unchanged. No statement is disputed.

## New nodes

None.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
