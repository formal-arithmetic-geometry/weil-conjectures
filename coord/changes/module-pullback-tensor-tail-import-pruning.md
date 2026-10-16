# module_pullback_tensor_iso_tail (redundant public imports)

## Reason

The second reading removes two redundant direct public imports. This is an import cleanup,
not a statement or definition change. The stage-3 preflight nevertheless requires an explicit
change record for public import removal. Both removed modules remain publicly reachable:

`Sheaf.CategoryTheory.RingedSiteModules` publicly imports
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`, which publicly imports
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`, which in turn publicly imports
`Mathlib.CategoryTheory.Sites.Sheafification`.

A recursive comparison of public-import graphs found exactly the same public closure before
and after removal, with no module added or lost. The theorem signature is byte-for-byte
unchanged. Every downstream statement and definition therefore keeps the same dependencies
and meaning; no target review is reopened. The proof-only imports used by the delivered proof
remain private. Three additional redundant imports are removed from the new recovery module;
that module has no pre-existing consumers and its public closure is also unchanged.

## Old

Old direct imports of the item, verbatim from the shared repository:

```lean
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
```

## New

```lean
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.CategoryTheory.AlgebraicInverseImageOfTransport
import Sheaf.Paper.RingedTopoiTensorComparisonConstruction
```

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.ModulePullbackTensorIsoE --uses
module_pullback_tensor_iso_tail` lists 188 transitive importers. Only the item and
`Sheaf.CategoryTheory.ModulePullbackTensorIso` mention the declaration. Each listed module is
recorded below. The identical public closure proves that no available declaration, instance,
notation, or definition disappears for any of them. The only direct importer is additionally
compiled unchanged against the delivered module. No consumer file is adapted.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.CategoryTheory.ModulePullbackTensorIsoE` | G4 | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.OpenDirectImageOverField` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.SmoothGenericDirectImage` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.AlgebraicGeometry.SmoothTensorDuality` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.CategoryTheory.ModulePullbackTensorIso` | unclaimed | Only direct importer; compiled unchanged against delivered dependency; same statement. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.Paper.CondensedLfpCoefficientModel` | A4 | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.Paper.ProjectionFormulaFiniteFree` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.Paper.ProjectionFormulaProjectiveSummand` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.Paper.ProjectionFormulaTotalization` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.Paper.RingedExchangeTensorCoherence` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.WeilSheaf.AffineCurveRangePositive` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.WeilSheaf.CohomologyGeometricConjugacy` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.WeilSheaf.CohomologyGeometricEquivalence` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `Sheaf.WeilSheaf.FiniteBoundaryPositive` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `TargetsCheck` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Defs` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DenseOpen` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.Weights` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.RationalStage` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.Adic.Localization` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationConstructible` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationFiniteTor` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.Statement` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.ArtinSchreierDual` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.ArtinSchreierFrobenius` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.ArtinSchreierPurity` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.ArtinSchreierTrace` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.BoundaryStalk` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.Cohomology` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.CohomologyExact` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.CohomologyShift` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.ComplexWeights` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.ConstantTwistCohomology` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.Defs` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.DenseOpen` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.DirectImageRestriction` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.DirectImageStalk` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.ExtensionByZero` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.FiniteEtaleLisse` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.Finiteness` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.Fourier` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Defs` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.TensorLisse` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.UpperStar` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierPlancherel` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierTateTwist` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierTateTwist.Transform` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierTrace` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierTraceAux` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.GeometricCoinvariants` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.GeometricallyConstant` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.GrothendieckLefschetz` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.HomologyShift` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.Localization` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.LocalizationRational` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriek` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerStar` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerStarComp` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerStarId` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerStarPairing` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerStarTensorPow` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.MiddleExtension` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.OpenImmersion` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.OpenImmersionRestriction` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.Operations` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.PoincareDuality` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.ProperCohomology` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.Realizable` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.StalkConstantTwist` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.StalkExtensionByZero` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.StalkInternalHom` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.StalkOpenImmersion` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.StalkTateTwist` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.StalkTensor` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.TateTwist` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.TateTwistCohomology` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.Tensor` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.TensorObjPairing` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.TensorPower` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.TraceFunctionCongr` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.TraceFunctionOps` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.TraceFunctionTensor` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.TraceSeries` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.WeilSheaf.UpperStarPointwise` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | Signature unchanged; identical transitive public imports; no adaptation. |

## Status

landed 20261016T073841-L-1112588 2026-10-16 (merge of deliver/G4/Sheaf.CategoryTheory.ModulePullbackTensorIsoE)
