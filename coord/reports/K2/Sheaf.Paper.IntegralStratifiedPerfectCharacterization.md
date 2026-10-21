## What changed

Separated the unchanged completed local-model definitions and exact realization into
`Sheaf.Paper.IntegralStratifiedPerfectModels`, publicly reexported by the original module.
Proved the cohomology characterization from the separate Proposition 6.6.11 criterion:
finite PID resolutions handle degree-zero sheaves; exact restriction and realization commute
with cohomology; Noetherian finiteness gives finite presentation; finite refinements of the
stratum covers give global bounds; bounded Postnikov devissage finishes the converse.
The common interface extraction is recorded in `coord/changes/K2-integral-local-model-interface.md`.
Existing public signatures and definition bodies are unchanged.

Also filled existing theorem holes in the unclaimed, directly used coefficient dependency
`Sheaf.Paper.BoundedConstructibleComplete`; see the proof-only support change record.
These establish the lifted integral coefficient properties and the exact realization and
its derived equivalence, and prove the canonical reduction mate invertible.
In the completed coefficient dependency, prove the normalized finite coefficient comparisons,
the concrete quotient tower, and preservation of K-flatness under scalar extension.

## Proved and sorry left

Closed the body of `AlgebraicGeometry.Scheme.integralStratifiedPerfectCharacterization`
(original node `lem-weil-pbc-integral-stratified-perfect-characterization`) by a complete
Lean proof. Added exactly one hole:
`AlgebraicGeometry.Scheme.integralCompletedLocalPerfectCriterion`
(node `lem-weil-pbc-integral-completed-local-perfect-criterion`), which is the separate
Proposition 6.6.11, only the first of the two equivalences of the original declaration.
This is a decomposition, not a net hole closure. Its combination with the proved resolution,
boundedness, local cohomology and Postnikov arguments is nontrivial Lean code.
The degree-zero finite-resolution argument and the global boundedness argument add no holes.
`AlgebraicGeometry.Scheme.integralStratifiedPerfectDetailed` remains the other original hole,
on the original characterization node. In the assigned module this leaves one original hole and one genuine separate source
theorem split off; one original body is closed. The supporting-module hole inventory is
recorded below. Definitions are concrete and unchanged.


Closed all seven pre-existing holes of the unclaimed supporting module
`Sheaf.Paper.BoundedConstructibleComplete`, with no new holes there:

- `AlgebraicGeometry.Scheme.pbcFunctionScalars_locallyBijective`
- `AlgebraicGeometry.Scheme.pbcAssociatedRestriction_exists`
- `AlgebraicGeometry.Scheme.pbcFunctionRealization_exact`
- `AlgebraicGeometry.Scheme.pbcDerivedFunctionRealization_equivalence`
- `AlgebraicGeometry.Scheme.pbcFunctionScalars_comp`
- `AlgebraicGeometry.Scheme.pbcFunctionReductionMap_isIso`
- `AlgebraicGeometry.Scheme.pbcCoefficientDatumProperties`

These belong to the existing coefficient/category nodes and are needed by the completed
criterion's concrete interface. The support change record is
`coord/changes/K2-integral-coefficient-support-proofs.md`.


In `Sheaf.Paper.AdicCoefficientDatumCompleted`, closed these existing holes without
adding any:

- `AlgebraicGeometry.Scheme.adicDatumFiniteCoefficientIso_exists`
- `AlgebraicGeometry.Scheme.adicDatumFiniteCoefficientIso_natural`
- `AlgebraicGeometry.Scheme.adicDatumQuotients_exists`
- `AlgebraicGeometry.Scheme.adicDatumExtension_kflat`

The unchanged remaining holes of that supporting module, all attached to
`def-weil-pbc-adic-coefficient-datum`, are:

- `AlgebraicGeometry.Scheme.adicDatumAdjunction_exists`
- `AlgebraicGeometry.Scheme.adicDatumOrdinaryTransition_exists`
- `AlgebraicGeometry.Scheme.adicDatumTowerDerived_exists`
- `AlgebraicGeometry.Scheme.adicDatumBalance_exists`
- `AlgebraicGeometry.Scheme.adicDatumComplexCounit_isIso`
- `AlgebraicGeometry.Scheme.adicDatumBalance_cocycle`

Its proof-only change record is
`coord/changes/K2-integral-completed-coefficient-proofs.md`.
Validation: the five changed/new modules and two unchanged consumers
(`SfIntegralStandardTruncations` and `StratifiedPerfectInternalHomCoproducts`) compile
in import order, with no warnings and each file below the 60-second limit. An interface
audit found all 112 existing public declaration headers unchanged (including the eight
verbatim moved declarations reexported by the parent).

The axiom audit of all eleven supporting proofs and the finite-PID resolution helper
reports only `propext`, `Classical.choice` and `Quot.sound`; its audit module compiles
in 2.7 seconds. The characterization still depends on `sorryAx` through the retained open
mathematics; it is a reduction.

Across the three existing delivered modules, twelve of nineteen original theorem bodies
are closed; one genuinely separate source theorem is added. Eleven supporting holes are
proved outright and the parent characterization is decomposed. Eight holes remain in the
whole packet, including the newly isolated criterion. No source-library file changes.

## No longer needed

The parent uses the finite-free-resolution and Postnikov ingredients directly in its own
standard localization; it does not need the source module
`WeilConjectures.CategoryTheory.DerivedCategory.PrincipalIdealDevissage`. Its declarations
remain untouched in the source library.

Removed these direct proof imports from the parent (including a duplicate countable-products
import). Their unneeded direct imports are pruned; dependencies required by Proposition 6.6.11
remain attached to its new node, and those of the still-open detailed comparison remain attached
to the original node. No upstream declaration or quarantined module is withdrawn.

- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.Paper.CompletedConstantAlgebraFlatQuotients`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`
- `Sheaf.Paper.ConstantModuleSectionProperties`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.Paper.BoundedConstructibleTower`
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
- `Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy`
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`
- `Sheaf.Paper.AdicCoefficientDatum`
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`
- `Sheaf.Paper.DerivedComplete`
- `Sheaf.CategoryTheory.RingedKoszulCompletionReflector`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity`
- `Sheaf.Paper.ProEtaleConstructibleSheaf`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.WeilCompletedTensorReflector`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore`

The two unit-route modules `ProEtaleSiteComparisonFiniteLevel` and
`IntrinsicFiniteTorsionConstructibility` remain proof imports of the completed criterion;
the source-unit route is retained.

No existing mathematical dependency is asserted globally unreachable: the retained completed
criterion and detailed comparison still need their completion and reduction theory.

## Where the brief, the DAG or earlier work was wrong

The existing algebraic PID devissage is tied to another localization universe. Reused its
finite-free-resolution argument in the standard localization used by the existing definitions;
the original source declaration is preserved. Slice restriction is representative-based, so
explicit localization-factorization isomorphisms are needed before using exact-functor APIs.
The terminal site object is canonically isomorphic to the base scheme, not definitionally the
base scheme. Both comparisons are proved. No mathematical statement is weakened.

## New nodes

`lem-weil-pbc-integral-completed-local-perfect-criterion` isolates the published Proposition
6.6.11 from the original node's combination with Proposition 6.8.11(3). It retains both
completion and compatible etale-origin clauses. Its full proof plan is the original steps 1-6.
The common Models module is a verbatim extraction of the original node's definitions;
the original attachment records it as a supporting module. The new definition node
`def-weil-pbc-integral-stratified-perfect-models` owns the extracted interface module;
it adds no declarations or proof holes beyond that verbatim relocation.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
