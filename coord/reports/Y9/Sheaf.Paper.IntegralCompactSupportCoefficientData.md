## What changed

Updated only `Sheaf.Paper.IntegralCompactSupportCoefficientData` and its existing
`def-pur-integral-compact-support-coefficient-data` node. Public signatures, public
imports and construction bodies remain unchanged.

- `modulePushComposition_existsUnique` takes the normalized module composition from
  `proEtaleRingDerivedPullbackComposition`. Sectionwise extensionality proves uniqueness.
- `projectionComparisons_existsUnique` constructs the two curried natural isomorphisms.
  A proved private lemma derives naturality of `openProjectionInverse` from adjunction
  naturality and tensor-comparison naturality. The existing
  `openProjectionInverse_isIso` supplies component invertibility.
- `completedPullMap_isIso` identifies the adjunct of `sfCompletedCoefficientMap` with
  the proved `coefficient_inverse_image_iso` from `SfCompleteDirectImageReduction`.
  Its proved `coefficient_direct_image_eq` fixes the normalization. The private proof
  import uses `import all` to access these helpers; it does not use that module's
  main reduction theorem.
- `completedPull_comp` and `completedChange_square` compare after every positive
  finite coefficient projection, using a proved private projection identity and
  faithful forgetfulness to the RingCat limit. The composition identity uses the
  proved constant inverse-image composition helper from
  `ProfiniteCoefficientInverseImage`, accessed with `import all`.

The original existential binder in `projectionComparisons_existsUnique` is unused in
its `True` property; its unchanged statement has a local unused-variable linter option.

The complete item module compiled cleanly through `lcompile.py` in 35.2 seconds.

Removed unused inherited private proof imports. No definition or statement repair,
consumer adaptation, new module, new node, or new hole is included.

## Proved and sorry left

Closed five of the original seven holes, all in namespace
`WeilConjectures.PurCompactSupport`:

- `modulePushComposition_existsUnique`.
- `projectionComparisons_existsUnique`.
- `completedPullMap_isIso`.
- `completedPull_comp`.
- `completedChange_square`.

Two original holes remain, with their original statements and documented proofs:

- `WeilConjectures.PurCompactSupport.openRestrictionMap_isIso`
  (`def-pur-integral-compact-support-coefficient-data`).
- `WeilConjectures.PurCompactSupport.openProjectionInverse_isIso`
  (`lem-sp-intrinsic-open-projection-invertible`).

Holes added: zero. Split-off statements: zero. The comparison-data proof uses the
retained open-projection theorem; it does not close that separate geometric hole.

## No longer needed

Removed these private imports from this item's module:

- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `WeilConjectures.RingTheory.FiniteOverCompleteRing`.
- `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Sheaf.Paper.ProjectionMateExact`.
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`.
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`.
- `Sheaf.CategoryTheory.DiagramSiteRealization`.
- `Mathlib.Algebra.Category.Grp.FilteredColimits`.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`.
- `Mathlib.CategoryTheory.Sites.Limits`.
- `Sheaf.Algebra.Homology.DiagramKFlatReplacements`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`.
- `Sheaf.Algebra.Homology.KFlat`.
- `WeilConjectures.Algebra.Homology.TowerEvaluationKInjective`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.CategoryTheory.StrictRoosComparison`.
- `Sheaf.Paper.NormalizedDVRTower`.
- `Sheaf.Paper.NormalizedDVREffectivity`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`.
- `Sheaf.Paper.SfIntegralCompactSupportConstructible`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`.
- `WeilConjectures.Compactification.CategoryBaseChange`.
- `Sheaf.Paper.RingedExchangeTensorCoherence`.
- `Sheaf.Paper.CompletedProjectionCoherence`.
- `Sheaf.Paper.CompletedPullbackAdjunction`.
- `Sheaf.Paper.CompletedOpenExchangeTransport`.
- `Sheaf.Paper.CompletedDirectImageLimits`.
- `Sheaf.Paper.DerivedAdjunctionShift`.
- `Sheaf.Paper.IntegralScalarExtensionWellDefined`.

These are import removals, not module withdrawals. No source-library declaration
is removed or changed. The public import surface remains verbatim, so no global
pruning claim is made for these modules. The retained open-projection hole still
needs its planned geometric dependencies; none is withdrawn from its node.
The broad coefficient-data node previously had no proof steps or proof dependencies;
it now records the actual composition, naturality and finite-projection arguments.
The unit route and both other nodes attached to this module remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The module contains seven holes, although its main node is classified as a
definition node and previously had no proof plan. Its existing module composition
and completed inverse-image statements can be obtained from existing normalized
library constructions. No new existence assumptions or arbitrary choices are needed.
The current module was present in `lean/` despite its historical rework quarantine
row; this delivery preserves it and all its declarations.

The declared open-projection dependencies use finite constant coefficients or a
slice-site tensor presentation, whereas this module accepts arbitrary ring-sheaf
coefficient identifications and the small pro-etale tensor models. The two original
open-geometry holes have not been hidden behind replacement statements.

A dependency audit found an existing cycle between
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent` in the shared DAG.
None of this delivery's added dependency edges has a path back to the item node;
the unrelated existing cycle is reported for maintenance and left untouched.

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
