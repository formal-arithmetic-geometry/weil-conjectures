# CategoryTheory.FilteredObject.enough_strict_filtered_injectives

## Reason

Complete the existing proof using private, proved helpers and additional proof-only imports.
The static interface comparison flags added command-level declarations, even though the
original public theorem signature and public imports are identical. This record documents
those commands and checks every downstream module. No mathematical statement or definition
used by a target is changed. No target requires renewed mathematical-statement review.

The finite-biproduct instance is registered only locally, to use the same finite-product
construction as the splitting theorem in this universe configuration. It exports no global
instance. All new definitions and theorems are private. The only new data definitions are
the explicitly constructed tail subobject and its decreasing filtration; neither contains
any proof placeholder or an arbitrary choice from an unproved existence statement.

## Old

The original file has no finiteBiproduct helper or local instance registration. Its options,
verbatim, are:

```lean
set_option autoImplicit false
set_option warn.sorry false
```

It has no `omit` command or declaration-local unused-variable setting. The public theorem
`CategoryTheory.FilteredObject.enough_strict_filtered_injectives` has the original signature
shown in the existing node's `lean.statement` and its proof is `by sorry`.

## New

```lean
set_option autoImplicit false

private theorem finiteBiproduct {K : Type} [Finite K] (J : K → C) : HasBiproduct J :=
  HasBiproduct.of_hasProduct J

attribute [local instance] finiteBiproduct
```

The private theorem `iso_map_factors` has `omit [Abelian C] in` because its proof uses only
the category structure; this command is scoped to that one helper. Immediately before the
original theorem's unchanged docstring and signature, the command is:

```lean
set_option linter.unusedVariables false in
```

This retains the original explicit hX and hY binders, whose hypotheses are not needed by
the proof. Every new declaration is private, and the original public theorem signature is
textually identical. Proof-only imports add
`Mathlib.Algebra.Homology.ShortComplex.ShortExact` and
`Mathlib.CategoryTheory.Abelian.CommSq`. Public imports remain identical. There is no
changed public signature or changed mathematical definition for consumers to adapt to.

## Users

`tools/downstream.py Sheaf.CategoryTheory.EnoughStrictFilteredInjectives --uses
CategoryTheory.FilteredObject.enough_strict_filtered_injectives` lists 78 transitive
importers and finds no downstream textual use of the theorem yet. The only direct importer
is `Sheaf.Algebra.Homology.FilteredLocalizationInjectiveModel`, whose planned proof uses
the existing theorem. It keeps the exact same theorem type. All downstream files therefore
keep their existing statements; no consumer file is delivered or adapted. Holder entries
below are read from the current claims and are informational only.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.EnoughStrictFilteredInjectives | F4 | Proof completed; original theorem type and public imports retained. |
| Sheaf.Algebra.Homology.FilteredDerivedHomCalculusUniverse | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.Algebra.Homology.FilteredGlobalHomExactAdjunction | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.Algebra.Homology.FilteredLocalizationInjectiveModel | D4 | Direct proof importer; no signature change or adaptation. |
| Sheaf.AlgebraicGeometry.DivisorTorsorBoundarySigns | B2 | Transitive importer; no semantic change or adaptation. |
| Sheaf.CategoryTheory.BoundedInjectiveFibreDescent | G3 | Transitive importer; no semantic change or adaptation. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.CartierClassAgreement | U5 | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.LocalizedTopChern | E5 | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.PurityDivisorClass | J7 | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Transitive importer; no semantic change or adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Transitive importer; no semantic change or adaptation. |
| TargetsCheck | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.Statement | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Transitive importer; no semantic change or adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Transitive importer; no semantic change or adaptation. |

## Status

landed 20261020T051235-L-1605666 2026-10-20 (merge of deliver/F4/Sheaf.CategoryTheory.EnoughStrictFilteredInjectives)
