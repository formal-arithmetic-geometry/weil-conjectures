# CategoryTheory.Over.DescentDataCategory

## Reason

The intermediate proof modules need the category without importing the theorem they help prove. Move its existing declarations unchanged to a common module. Re-export the module publicly from the original item so all downstream imports still find the same declarations. No target statement or definition changes meaning.

## Old

In `Sheaf.AlgebraicGeometry.FpqcSingletonFullyFaithful`:

```lean
structure DescentDataCategory {S X : Scheme.{u}} (a : X ⟶ S) where
  V : Over X
  datum : DescentDatum a V

namespace DescentDataCategory

variable {S X : Scheme.{u}} {a : X ⟶ S}

/-- Morphisms over `X` compatible with the two descent data. Source: Stacks Project,
Descent, Definition 35.34.1 (3) (Tag 023V)
(blueprint: lem-galois-fpqc-singleton-fully-faithful-0241). -/
@[ext]
structure Hom (A B : DescentDataCategory a) where
  hom : A.V ⟶ B.V
  commutes : ∀ {T : Scheme.{u}} (f₀ f₁ : T ⟶ X) (h : f₀ ≫ a = f₁ ≫ a)
    (z : Over.mk f₀ ⟶ A.V),
    B.datum.transport f₀ f₁ h (z ≫ hom) =
      A.datum.transport f₀ f₁ h z ≫ hom

instance : Category (DescentDataCategory a) where
  Hom := Hom
  id A :=
    { hom := 𝟙 A.V
      commutes := by
        intro T f₀ f₁ h z
        simp only [Category.comp_id] }
  comp := fun {A B C} f g =>
    { hom := f.hom ≫ g.hom
      commutes := by
        intro T i j h z
        change C.datum.transport i j h ((z ≫ f.hom) ≫ g.hom) =
          (A.datum.transport i j h z ≫ f.hom) ≫ g.hom
        rw [g.commutes, f.commutes] }
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

end DescentDataCategory

```

## New

The identical declarations above now live in `Sheaf.AlgebraicGeometry.SchemeDescentDataCategory`. The original module contains:

```lean
public import Sheaf.AlgebraicGeometry.SchemeDescentDataCategory
```

## Users

`tools/downstream.py` reports 150 transitive importers and six modules mentioning the category. The five unchanged downstream source users below keep exactly the same names, signatures, definitions, instance, and public import closure; no adaptation is needed. All other transitive importers likewise require no source change. New proof modules import the common category directly.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FpqcSingletonFullyFaithful | T2 | definitions relocated; publicly re-exported |
| Sheaf.AlgebraicGeometry.DescentPullbackCanonicalIso | not edited | unchanged statements and imports |
| Sheaf.AlgebraicGeometry.FiniteEtaleDescentData | not edited | unchanged statements and imports |
| Sheaf.AlgebraicGeometry.FiniteEtaleDescentDataExistence | not edited | unchanged statements and imports |
| Sheaf.AlgebraicGeometry.FiniteEtaleDescentEssentiallySurjective | not edited | unchanged statements and imports |
| Sheaf.AlgebraicGeometry.FiniteEtaleDescentFullyFaithful | not edited | unchanged statements and imports |
| Sheaf.AlgebraicGeometry.SchemeDescentDataCategory | T2 | receives identical definitions |
| Sheaf.AlgebraicGeometry.DescentPullbackConstruction | T2 | new construction statement |
| Sheaf.AlgebraicGeometry.FpqcDescentUnderlyingMorphism | T2 | new unique underlying descent statement |
| Sheaf.AlgebraicGeometry.FpqcDescentMorphismCompatibility | T2 | new datum compatibility statement |

| Sheaf.AlgebraicGeometry.AffineFpqcDescent | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.DescentPullbackCanonicalIso | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteEtaleDescent | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteEtaleDescentData | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteEtaleDescentDataExistence | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteEtaleDescentEssentiallySurjective | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteEtaleDescentFullyFaithful | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.FpqcDescendingTypesMorphisms | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.FpqcRefinementFullyFaithful | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.GenusInvariant | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.InvariantAffineDescentGluing | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAssembly | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | not edited | unchanged declarations publicly re-exported; no adaptation |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | not edited | unchanged declarations publicly re-exported; no adaptation |
| TargetsCheck | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.AlgebraicGeometry.EffectiveDescent | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.FourierTransform.Defs | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.FourierTransform.Inversion | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.FourierTransform.Perverse | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.FourierTransform.Properties | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseChange | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.FourierTransform.Properties.Stalk | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not edited | unchanged declarations publicly re-exported; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not edited | unchanged declarations publicly re-exported; no adaptation |

Second-reading preflight also lists the following modules as users of the relocated
`Hom`. They contain no `DescentDataCategory` reference; the conservative name scan
also matches other `Hom` names. They require no adaptation, and the public names
remain available as before.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | not edited | no descent-category reference; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | not edited | no descent-category reference; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | not edited | no descent-category reference; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | not edited | no descent-category reference; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | not edited | no descent-category reference; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | not edited | no descent-category reference; no adaptation |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | not edited | no descent-category reference; no adaptation |
| WeilConjectures.SixFunctors.Etale.Gabber | not edited | no descent-category reference; no adaptation |

## Status

landed 20261012T070553-L-3478150 2026-10-12 (merge of deliver/T2/Sheaf.AlgebraicGeometry.FpqcSingletonFullyFaithful)
