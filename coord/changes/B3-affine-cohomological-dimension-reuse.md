# Affine cohomological-dimension theorem reuse

## Reason

Repair of the returned head: provide a fully proved explicit-dimension variant in a Sheaf
module and remove the source module's direct import of the statement named in the return.

The assigned source declaration duplicates the existing affine theorem in the Sheaf root,
with a different cohomology spelling and an upper dimension bound. Reuse that theorem rather
than add a second geometric induction. Its module is unclaimed. Its private proof imports are
unused by its existing whole-theorem sorry; three of them reach the source declaration and
would make the reuse cyclic. Remove the unused private proof imports. Retain every public
import, declaration, signature, visibility and existing proof of that module.

## Old

The source declaration had a whole-theorem sorry. The Sheaf theorem had these private imports:

```text
import Mathlib.RingTheory.NoetherNormalization
import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
import Sheaf.AlgebraicGeometry.DimensionPreservedFieldExtension
import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimensionGroundField
import Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.Sites.ArbitraryCurveCohomologicalDimension
import Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModel
import Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Sheaf.FieldTheory.OneVariableFieldCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit
import Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.GeometricFiberFinite
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve
import Sheaf.CategoryTheory.GrothendieckSpectralSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.SupportDimensionUnion
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import Sheaf.AlgebraicGeometry.TorsionFilteredUnion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
import WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.AffineLineProjectionStalkBound
import Sheaf.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk
```

## New

The source declaration privately imports
`Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionBound` instead of the
returned direct import of `AffineTorsionCohomologicalDimensionOfAffine`.
The new variant `hasTorsionEtaleCohomologicalDimensionLE_of_isAffine_of_dimension_le` is
fully proved in the Sheaf tree: it combines the existing theorem's empty and nonempty clauses
with the explicit bound on Krull dimension. It adds no sorry. The source proof applies it
between two applications of the proved Ext/derived-sections comparison. All existing
signatures, visibility, definitions, and public imports stay unchanged.

The adapted Sheaf theorem retains exactly its four public imports and its existing named sorry.
Its complete geometric proof plan and all unit-level obligations remain in the DAG.
The new variant's import of that theorem is private; its public imports expose only the
notions appearing in its own statement.

## Users

All entries below retain identical public import closures and declarations. The three direct
importers are checked independently against the sandbox overlay. Other consumers need no edit.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.AlgebraicGeometry.AffineCurveCohomologicalDimension | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.AlgebraicGeometry.AffineSupportVanishing | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.AlgebraicGeometry.ProperProjectionFormula | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.AlgebraicGeometry.RelativeDimensionOneInduction | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.AlgebraicGeometry.UniversalCurveTestVanishing | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Same signatures and public imports; no consumer edit. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.Statement | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.HomologyShift | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same signatures and public imports; no consumer edit. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same signatures and public imports; no consumer edit. |

## Status

landed 20261017T013731-L-112670 2026-10-17 (merge of deliver/B3/WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension)
