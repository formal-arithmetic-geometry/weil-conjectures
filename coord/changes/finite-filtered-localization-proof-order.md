# CategoryTheory.finiteFiltered_hasFiniteProducts

## Reason

The proof that a direct-sum filtration has injective graded objects uses the additive
graded functor. Move the finite-product theorem and its derived zero/biproduct instances
after `filteredEvaluation_additive`. This reorders the two existing instance attributes.
Private proof helpers construct the actual binary sum and its maps; four private
instances express the elementary closure properties of the private graded-acyclic
predicate. Declaration-local `open ZeroObject in` only supplies object-zero notation
inside the private helpers. No public statement, definition body or public import changes.
This record is supplied because the static preflight classifies command reordering as
an interface change requiring independent reading.

## Old

```lean
attribute [instance] finiteFiltered_hasFiniteProducts
-- filtered evaluation and its additivity occur later
attribute [instance] filteredEvaluation_additive
```

```lean
theorem finiteFiltered_hasFiniteProducts (B : Option (ℤ × ℤ)) (inj : Bool) :
    HasFiniteProducts (FiniteFilteredObjects C B inj) := by
  sorry
```

## New

```lean
attribute [instance] filteredEvaluation_additive
-- explicit product constructions and their proofs
attribute [instance] finiteFiltered_hasFiniteProducts
```

```lean
theorem finiteFiltered_hasFiniteProducts (B : Option (ℤ × ℤ)) (inj : Bool) :
    HasFiniteProducts (FiniteFilteredObjects C B inj) := by
  have := finiteFiltered_terminal C B inj
  have : ∀ {K L : FiniteFilteredObjects C B inj}, HasBinaryProduct K L :=
    fun {K L} ↦ finiteFiltered_binaryProduct C B inj K L
  have := hasBinaryProducts_of_hasLimit_pair (C := FiniteFilteredObjects C B inj)
  exact hasFiniteProducts_of_has_binary_and_terminal
```

## Users

`tools/downstream.py` lists the following downstream modules. Their meanings are
unchanged: all public declarations retain their exact signatures and definition bodies;
all original public imports remain. `--uses finiteFiltered_hasFiniteProducts` finds only
the item itself. The private construction names are used only in proofs of the item.
There are no adapted modules and no target statement or target definition changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.FiniteFilteredLocalization | E2 | Proof completion and declaration reordering only. |
| Sheaf.Algebra.Homology.BoundedFilteredLocalizationEmbedding | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Algebra.Homology.FilteredConeLocalization | A8 | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Algebra.Homology.FilteredDerivedHomCalculus | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Algebra.Homology.FilteredDerivedHomCalculusUniverse | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Algebra.Homology.FilteredGlobalHomExactAdjunction | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Algebra.Homology.FilteredLocalizationInjectiveModel | D4 | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Algebra.Homology.FilteredTruncationData | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Algebra.Homology.FilteredTruncationTriangle | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Algebra.Homology.UniformFilteredHomotopyLocalization | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Algebra.Homology.UniformFilteredTruncation | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorTorsorBoundarySigns | B2 | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.AlgebraicGeometry.LocalizationFiltrationDescent | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleLocalizationFilteredSection | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.CategoryTheory.BoundedInjectiveFibreDescent | G3 | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.CategoryTheory.FilteredBifunctorGradedComparison | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.CategoryTheory.FilteredFunctorGradedComparison | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | U5 | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | E5 | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | J7 | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| TargetsCheck | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.Statement | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No signature, definition, visibility or public-import change; no adaptation. |

## Status

landed 20261020T051210-L-1592588 2026-10-20 (merge of deliver/E2/Sheaf.Algebra.Homology.FiniteFilteredLocalization)
