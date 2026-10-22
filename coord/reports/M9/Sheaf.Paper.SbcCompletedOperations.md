## What changed

Filled the fifteen original proof holes in `lean/Sheaf/Paper/SbcCompletedOperations.lean`.
Private proved helpers supply the reflection Hom bijections, normalized comparisons,
finite coefficient completeness and the exchange rectangle. The existing statements,
public imports and definition bodies are preserved. The node's proof and dependencies
now follow these arguments.
The preflight-requested command record is
`coord/changes/sbc-completed-operations-proof-elaboration.md`; it audits the local
elaboration controls and all 307 transitive consumers. No consumer is adapted.

Validation: the complete item compiled cleanly through `lcompile.py` in 42.1 seconds,
within the normal 60-second file limit. All 74 original declaration signatures and
all 51 original non-theorem bodies are unchanged; the file contains no `sorry`.

## Proved and sorry left

Original holes closed (15):

- `WeilConjectures.sbcOrdinaryDerivedIso_exists`
- `WeilConjectures.sbcOperations_preserveComplete`
- `WeilConjectures.sbcOperations_linear`
- `WeilConjectures.sbcAdjunction_exists`
- `WeilConjectures.sbcCoefficientComp`
- `WeilConjectures.sbcPullComp_exists`
- `WeilConjectures.sbcOrdinaryReductionMap_isIso`
- `WeilConjectures.sbcCompletionUnit_reduction_isIso`
- `WeilConjectures.sbcReductionComparisons_isIso`
- `WeilConjectures.sbcTheta_exists`
- `WeilConjectures.sbcFiniteCoefficientSquare`
- `WeilConjectures.sbcCompletedOperations_linear_natural_exchange`
- `WeilConjectures.sbcStrictSourceComparison_exists`
- `WeilConjectures.sbcStrictTargetComparison_exists`
- `WeilConjectures.sbcCompletedExchange_strictLimit`

No `sorry` remains in the item; no holes or split modules are added. Imported statements
retain their existing proof status. These are proofs from the existing library interfaces,
not claims that the complete transitive dependency closure is axiom-free.

## No longer needed

Removed direct proof imports:

- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointSquareComparison`
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`
- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.AdicCoefficientDatum`
- `Sheaf.Paper.CompletedPullbackReduction`
- `Sheaf.Paper.CompletedRlimFunctor`
- `Sheaf.Paper.CondensedAmbientExchange`
- `Sheaf.Paper.IntrinsicCompletionCompleted`
- `Sheaf.Paper.PerfectProjectionFormula`
- `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `WeilConjectures.Algebra.Homology.TowerEvaluationKInjective`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The proof does not use the planned SBC helper nodes
`lem-sbc-koszul-fibre-linear-descent`, `lem-sbc-ambient-operations-scalar-linearity`,
`lem-sbc-reflector-adjunction-unit-formulas`,
`lem-sbc-reflected-compositor-unit-normalization`,
`lem-sbc-reflector-square-mate-factorization`,
`lem-sbc-unbounded-exact-adjunction-square`, and
`lem-sbc-strict-quotient-exchange-unit-equation`.
Their arguments are supplied by the existing actual-operation interfaces and private
categorical calculations. The diagram-site evaluation route is unnecessary: the finite
mate cube and the explicit unit equations establish the required equalities directly.
No source-library declaration or module is withdrawn. Removed direct imports may still
be needed transitively by the interfaces used here.

Obsolete top-level tool approvals removed from the node (retained approvals keep
their original order):

- `lem-weil-l-adic-extension-integers-dvr`
- `lem-weil-pbc-diagram-site-realization`
- `lem-weil-pbc-ringed-topoi-derived-pullback`
- `prop-pur-kinjective-resolutions-exist`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-pc-pre-derived-adjoint-functors-general`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-ringed-exchange-tensor-coherence`
- `lemma-weil-pbc-perfect-projection-formula`
- `lem-weil-pbc-ring-sheaf-change-adjunction`
- `prop-weil-pbc-rlim-functoriality`
- `lem-weil-tower-evaluation-kinjective`
- `lem-pc-kflat-resolution`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-kun-derived-adjoint-square-comparison`
- `lem-weil-valued-dvr-finite-quotients`
- `lem-weil-linear-abelian-derived-category`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lem-weil-pbc-conjugate-iso-unit-equation`
- `lem-weil-pbc-ordered-exchange-coefficient-comparison`
- `lem-sp-completion-mate-comparison`
- `prop-weil-pbc-koszul-reconstruction`
- `lem-sbc-ambient-operations-scalar-linearity`
- `lem-weil-proetale-countable-products-exact`
- `lem-sfb-derived-composition-adjunction-normalization`

## Where the brief, the DAG or earlier work was wrong

The plan's specialized SBC intermediate lemmas are unnecessary for this assembly.
Existing actual completed-operation interfaces already supply the needed reflection
and linearity data. The finite exchange argument uses the inverse orientation of the
ordinary square comparison; this orientation is kept explicitly when applying the mate
cube. Equality of maps is obtained from the normalized unit equations and Hom bijections,
never from equality of finite evaluations alone. There is no statement or definition repair.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
