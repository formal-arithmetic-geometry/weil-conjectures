## What changed

Replaced 15 of the 17 existing proof holes in
`Sheaf.Paper.CompletedFiniteExchangeCoordinates`. Constructed the direct-image comparison
by identity linear maps using the finite coefficient projection square. Constructed the
reduction-level comparison by scalar-restriction composition, identity on sections.
Transported the existing invertible scalar-change mate through uniqueness of left adjoints.
Composed existing instances for the remaining finiteness, additivity, exactness and zero-map
claims. No declaration signature or definition body changed.

Validation: the complete module compiles without warnings using lcompile.py (13.1 seconds).
Earlier queue timeouts were retried; no compiler limit was changed.

## Proved and sorry left

The 15 existing holes closed are:

- `AlgebraicGeometry.Scheme.cbcFiniteRing_finite`
- `AlgebraicGeometry.Scheme.cbcFiniteDirectRes_existsUnique`
- `AlgebraicGeometry.Scheme.cbcFinitePullRes_isIso`
- `AlgebraicGeometry.Scheme.cbcFiniteReductionModule_additive`
- `AlgebraicGeometry.Scheme.cbcFiniteLevel_existsUnique`
- `AlgebraicGeometry.Scheme.cbcFiniteSource_additive`
- `AlgebraicGeometry.Scheme.cbcFiniteSource_limits`
- `AlgebraicGeometry.Scheme.cbcFiniteSource_colimits`
- `AlgebraicGeometry.Scheme.cbcFiniteTarget_additive`
- `AlgebraicGeometry.Scheme.cbcFiniteTarget_limits`
- `AlgebraicGeometry.Scheme.cbcFiniteTarget_colimits`
- `AlgebraicGeometry.Scheme.cbcFiniteSourceModel_preservesZeroMorphisms`
- `AlgebraicGeometry.Scheme.cbcFiniteTargetModel_preservesZeroMorphisms`
- `AlgebraicGeometry.Scheme.cbcSourceLevel_preservesZeroMorphisms`
- `AlgebraicGeometry.Scheme.cbcTargetLevel_preservesZeroMorphisms`

Two original holes remain, both attached to
`def-cbc-completed-finite-exchange-coordinates`:

- `AlgebraicGeometry.Scheme.cbcFiniteOpenRestriction_existsUnique`
- `AlgebraicGeometry.Scheme.cbcFiniteOpenRes_isIso`

No holes added; no split-off statements. All 15 replacement proofs compile.

## No longer needed

Removed unused private proof-plan imports:

- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`
- `Sheaf.Algebra.Homology.DiagramKFlatReplacements`
- `Sheaf.SixFunctors.OpenTensorNormalization`

Their corresponding nodes `lem-weil-pbc-constant-completion-equivalence`,
`lem-pur-site-restriction-module-adjunction-exact`,
`lem-weil-pbc-ringed-topoi-module-adjunction`,
`lem-weil-pbc-localize-ringed-site-morphism`, `lem-weil-pbc-diagram-kflat-replacements`
and `lem-sf-open-tensor-normalization` are not invoked directly by the new proofs.
Existing public statement imports remain; this does not claim these modules are globally
unreachable. No module is withdrawn. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The item is a definition node whose initial proof and proof_deps were empty, despite its
17 theorem holes. The node copy now records the arguments and the two retained obligations.
The ordinary algebraic and instance obligations need no further split.

Searches actually run: leanfinder for restriction commuting with sheaf module pullback
returned Mathlib scalar-restriction section formulas; loogle for restrictScalars/comp
returned ModuleCat.restrictScalarsComp'App; the launcher grep search returned generic
restriction-of-scalars results. Local rg searches found the already-proved ring-sheaf
scalar-change mate and completedCoefficient_isIso helper. No new mathematical statement
was introduced.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
