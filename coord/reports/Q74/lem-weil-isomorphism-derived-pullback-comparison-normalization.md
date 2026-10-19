## Worker report

I repaired the returned packet by replacing the arbitrary endofunctors `R`, `L` and
arbitrary adjunction `adj` with the canonical coefficient calculus supplied by
`CoefficientDerivedSystemCalculus`.  The theorem now binds `S` and its coherence
witness `hS`; its reduction is `S.reduction`, its strict-system limit is
`coefficientSequenceLimit l E Y`, and its unit is exactly `S.adjunction.unit`.
The output is therefore the specified comparison
`P_g M ≅ G((S.reduction ⋙ coefficientSequenceLimit).obj M)`.

The module also defines `strictReductionConeNormalization`.  This is the recorded
`CoefficientReductionModels` interface of `S.reductionModel`: for every flat-term
K-flat representative it supplies one strict quotient-system complex, the
representative comparison, and the equations for every quotient transition.  The
comparison equation in the theorem is an equality of the complete derived morphisms,
so it fixes both Roos-cone coordinates, including the zero shifted coordinate.  The
naturality clause is the resolution-independent descent of this strict construction
along arbitrary derived morphisms.  The final inverse is asserted only under
`IsDerivedCompleteUnrestricted`, as in the node.

The binders render the node as follows.

* `l`, `Fact l.Prime`, `E`, `Field E`, `Algebra ℚ_[l] E`, and
  `FiniteDimensional ℚ_[l] E` are the prime and finite coefficient extension.
* `{X Y}`, `g`, `[IsIso g]`, `hX`, and `hY` are exactly the scheme isomorphism and
  invertibility hypotheses of the specified pullback comparison.
* `S` and `hS` are the canonical simultaneous reduction/strict-system-limit calculus
  and its coherence witness from `coefficientDerivedSystemEvaluationCalculus`.
  In particular the source and target of the adjunction are the completed-module
  derived category and the strict quotient-system derived category; they are no
  longer two unrelated endofunctors on one category.
* `N` and `hN` are an arbitrary ambient object and the derived-completeness hypothesis.
* `θ` is a family of isomorphisms from the specified integral pullback to inverse
  image of the canonical completion.  The first conjunct identifies the specified
  `inverseImagePullbackComparisonDerived` with the actual adjunction unit.  The
  second conjunct is naturality for every derived morphism.  The
  `strictReductionConeNormalization` conjunct records the strict representative and
  transition equations.  The last existential gives the two-sided inverse for the
  specified comparison at `N` and its unit normalization.

The dependency declarations used are:

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`,
  `WeilConjectures.integralConstantToCompletionOfUniverses`.
* `Sheaf.Paper.SemilinearDerivedSections`,
  `WeilConjectures.SemilinearSections.semilinearDerivedSections`.
* `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`,
  `WeilConjectures.coefficientDerivedSystemEvaluationCalculus` and its
  `CoefficientDerivedSystemCalculus` / `CoefficientDerivedSystemCoherence` fields.
* `Sheaf.Paper.IntegralDerivedOperationsOnSlices`,
  `WeilConjectures.IntegralOnSlice.completedTensor`.
* `Sheaf.Paper.InverseImagePullbackComparisonDerived`,
  `AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived`.
* `Sheaf.Paper.DerivedCompleteUnrestricted`,
  `WeilConjectures.IsDerivedCompleteUnrestricted`.
* `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
* `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`,
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`.

Edge cases checked: the identity isomorphism `g = 𝟙 _`; the zero complex; empty
schemes; the prime `l = 2`; incomplete objects (where no inverse is claimed); and a
complete finite-free object (where the unit inverse gives the displayed `κinv`).
The statement keeps all positive quotient levels and does not impose boundedness,
constructibility, or finite Tor amplitude.

Searches rerun or retained from the packet:

* `msearch.py ... leanfinder "specified inverse-image pullback comparison equals
  completion unit for an isomorphism of schemes"`: generic pullback/isomorphism hits,
  no strict-tower normalization.
* `msearch.py ... loogle "CategoryTheory.Iso, IsDerivedCompleteUnrestricted,
  inverseImagePullbackComparisonDerived"`: no exact hit.
* `msearch.py ... grep "inverseImagePullbackComparisonDerived|completionUnit|
  comparisonNormalization"`: no declaration of this item.
* `rg -n` over `WeilConjectures/` and project `lean/Sheaf/`: found the recorded
  comparison and coefficient-calculus interfaces, but no declaration of this node.
* `grep -rl` for the node id: no existing declaration.

No `STATEMENT-DISPUTED` flag is needed.

## Second reading by Q74

I reread the node statement, the returned review, and the complete signatures and
source docstrings of the coefficient calculus, inverse-image comparison,
completion, strict Roos, and K-flat-resolution dependencies.  The repaired Lean
signature now matches every hypothesis and conclusion: the canonical reduction,
canonical limit, and actual adjunction unit are all fields of `S`; the strict
representative and quotient-transition interface is the explicit
`strictReductionConeNormalization` conjunct; the equality is at the whole derived
morphism level; naturality records descent independent of a chosen resolution; and
completeness is used only for the two-sided inverse.  The theorem proof remains
`sorry`, as required for stage 2.

## Maintainer review fix (2026-10-18)

The maintainer's second reader removed `strictReductionConeNormalization` and its
conjunct. The definition was only another name for
`CoefficientReductionModels l E Y S.reduction S.reductionEvaluation`, which is the
type of the field `S.reductionModel`. So the conjunct holds by `S.reductionModel`
(this was checked by compiling it). It does not involve `g` or `θ`, and it says
nothing new. Removing it leaves the mathematical statement unchanged. The reviewer
also rewrote the module and theorem docstrings. The old docstrings still named the
removed binders `R`, `L` and `adj`, described the conjuncts wrongly, and attributed
invertibility of the unit to `def-weil-derived-complete`. The new docstrings follow
the node's nine proof steps and the lemmas cited in each step, including
`lem-weil-finite-free-completed-scalar-comparison` for step 9. The unused universe
`v` was also removed.
