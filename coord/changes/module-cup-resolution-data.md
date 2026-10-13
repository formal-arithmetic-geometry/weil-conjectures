# ModuleCupResolutionData

## Reason

Factor the existing resolution-data definitions into a lower module so that
independently proveable existence and invariance statements can import them
without importing the theorem they help prove. No definition, structure field,
universe, declaration name, visibility, or target statement changes. The moved
declarations are publicly re-exported by their original importing module.
The original three public import paths remain reachable. The direct
TensorSection import is redundant because ModuleCupResolutionData exports it.

## Old

In Sheaf.Paper.ModuleCohomologyCupProduct, the following block was declared:

```lean
/-- The class of a cocycle, using Mathlib's kernel description of the cycles.
Source: Stacks, section-cup-product (blueprint: def-sc-module-cohomology-cup-product). -/
def cupCycleClass {R : Type uM} [Ring R] (K : CochainComplex (ModuleCat.{uM} R) ℕ)
    (n : ℕ) (z : (K.sc n).moduleCatLeftHomologyData.K) : K.homology n :=
  (K.sc n).homologyπ ((K.sc n).moduleCatCyclesIso.inv z)

/-- A resolution that computes module cohomology, with a comparison to an injective
resolution over the original coefficient sheaf. The global comparison must induce
isomorphisms; this holds, in particular, for flasque resolutions.
Source: Stacks, Tags 01DZ and 0FKV (blueprint: def-sc-module-cohomology-cup-product). -/
structure CupAcyclicResolution {X : Scheme.{uM}} (F : X.Modules) where
  K : CochainComplex X.Modules ℕ
  augmentation : (CochainComplex.single₀ X.Modules).obj F ⟶ K
  quasiIso : QuasiIso augmentation
  I : InjectiveResolution F
  comparison : K ⟶ I.cocomplex
  over : augmentation ≫ comparison = I.ι
  computes : ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ) |>.map comparison) n)

/-- The cohomology class represented by a global cocycle in an acyclic resolution.
Source: Stacks, Tags 01DZ and 0FKV (blueprint: def-sc-module-cohomology-cup-product). -/
def CupAcyclicResolution.class {X : Scheme.{uM}} {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ)
    (z : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K) :
    (RingedSpace.moduleCohomology X.toRingedSpace n).obj F :=
  letI : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  letI := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv
    (HomologicalComplex.homologyMap
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).map D.comparison) n
      (cupCycleClass _ n z))

/-- A sectionwise O-linear chain pairing of three nonnegative acyclic resolutions,
restricting in degree zero to the ordinary tensor of coefficient sections.
The sign in Leibniz is the total tensor sign. No compatibility of cup products on
cohomology is assumed in this data.
Source: Stacks, section-cup-product and Tag 0FKV
(blueprint: def-sc-module-cohomology-cup-product). -/
structure CupResolutionPairing {X : Scheme.{uM}} (F G : X.Modules) where
  left : CupAcyclicResolution F
  right : CupAcyclicResolution G
  target : CupAcyclicResolution (F ⊗ G)
  pair : ∀ (r s : ℕ) (V : X.Opens),
    Γ(left.K.X r, V) →ₗ[Γ(X, V)] Γ(right.K.X s, V) →ₗ[Γ(X, V)]
      Γ(target.K.X (r + s), V)
  restriction : ∀ (r s : ℕ) (V W : X.Opens) (h : W ≤ V)
    (a : Γ(left.K.X r, V)) (b : Γ(right.K.X s, V)),
    (target.K.X (r + s)).presheaf.map (homOfLE h).op (pair r s V a b) =
      pair r s W ((left.K.X r).presheaf.map (homOfLE h).op a)
        ((right.K.X s).presheaf.map (homOfLE h).op b)
  leibniz : ∀ (r s : ℕ) (V : X.Opens)
    (a : Γ(left.K.X r, V)) (b : Γ(right.K.X s, V)),
    (target.K.d (r + s) (r + s + 1)).val.app (op V) (pair r s V a b) =
      (eqToHom (congrArg (fun n ↦ target.K.X n)
          (by omega : r + 1 + s = r + s + 1))).val.app (op V)
        (pair (r + 1) s V ((left.K.d r (r + 1)).val.app (op V) a) b) +
      (-1 : ℤ) ^ r •
        (eqToHom (congrArg (fun n ↦ target.K.X n)
            (by omega : r + (s + 1) = r + s + 1))).val.app (op V)
          (pair r (s + 1) V a ((right.K.d s (s + 1)).val.app (op V) b))
  augmentation_pair : ∀ (V : X.Opens) (a : Γ(F, V)) (b : Γ(G, V)),
    pair 0 0 V ((left.augmentation.f 0).val.app (op V) a)
        ((right.augmentation.f 0).val.app (op V) b) =
      (target.augmentation.f 0).val.app (op V) (tmulSection a b)
```

## New

The block is in Sheaf.Paper.ModuleCupResolutionData with unchanged declarations;
only the blueprint docstring tags identify the newly factored data node:

```lean
/-- The class of a cocycle, using Mathlib's kernel description of the cycles.
Source: Stacks, section-cup-product (blueprint: def-sc-module-cup-resolution-data). -/
def cupCycleClass {R : Type uM} [Ring R] (K : CochainComplex (ModuleCat.{uM} R) ℕ)
    (n : ℕ) (z : (K.sc n).moduleCatLeftHomologyData.K) : K.homology n :=
  (K.sc n).homologyπ ((K.sc n).moduleCatCyclesIso.inv z)

/-- A resolution that computes module cohomology, with a comparison to an injective
resolution over the original coefficient sheaf. The global comparison must induce
isomorphisms; this holds, in particular, for flasque resolutions.
Source: Stacks, Tags 01DZ and 0FKV (blueprint: def-sc-module-cup-resolution-data). -/
structure CupAcyclicResolution {X : Scheme.{uM}} (F : X.Modules) where
  K : CochainComplex X.Modules ℕ
  augmentation : (CochainComplex.single₀ X.Modules).obj F ⟶ K
  quasiIso : QuasiIso augmentation
  I : InjectiveResolution F
  comparison : K ⟶ I.cocomplex
  over : augmentation ≫ comparison = I.ι
  computes : ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ) |>.map comparison) n)

/-- The cohomology class represented by a global cocycle in an acyclic resolution.
Source: Stacks, Tags 01DZ and 0FKV (blueprint: def-sc-module-cup-resolution-data). -/
def CupAcyclicResolution.class {X : Scheme.{uM}} {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ)
    (z : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K) :
    (RingedSpace.moduleCohomology X.toRingedSpace n).obj F :=
  letI : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  letI := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv
    (HomologicalComplex.homologyMap
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).map D.comparison) n
      (cupCycleClass _ n z))

/-- A sectionwise O-linear chain pairing of three nonnegative acyclic resolutions,
restricting in degree zero to the ordinary tensor of coefficient sections.
The sign in Leibniz is the total tensor sign. No compatibility of cup products on
cohomology is assumed in this data.
Source: Stacks, section-cup-product and Tag 0FKV
(blueprint: def-sc-module-cup-resolution-data). -/
structure CupResolutionPairing {X : Scheme.{uM}} (F G : X.Modules) where
  left : CupAcyclicResolution F
  right : CupAcyclicResolution G
  target : CupAcyclicResolution (F ⊗ G)
  pair : ∀ (r s : ℕ) (V : X.Opens),
    Γ(left.K.X r, V) →ₗ[Γ(X, V)] Γ(right.K.X s, V) →ₗ[Γ(X, V)]
      Γ(target.K.X (r + s), V)
  restriction : ∀ (r s : ℕ) (V W : X.Opens) (h : W ≤ V)
    (a : Γ(left.K.X r, V)) (b : Γ(right.K.X s, V)),
    (target.K.X (r + s)).presheaf.map (homOfLE h).op (pair r s V a b) =
      pair r s W ((left.K.X r).presheaf.map (homOfLE h).op a)
        ((right.K.X s).presheaf.map (homOfLE h).op b)
  leibniz : ∀ (r s : ℕ) (V : X.Opens)
    (a : Γ(left.K.X r, V)) (b : Γ(right.K.X s, V)),
    (target.K.d (r + s) (r + s + 1)).val.app (op V) (pair r s V a b) =
      (eqToHom (congrArg (fun n ↦ target.K.X n)
          (by omega : r + 1 + s = r + s + 1))).val.app (op V)
        (pair (r + 1) s V ((left.K.d r (r + 1)).val.app (op V) a) b) +
      (-1 : ℤ) ^ r •
        (eqToHom (congrArg (fun n ↦ target.K.X n)
            (by omega : r + (s + 1) = r + s + 1))).val.app (op V)
          (pair r (s + 1) V a ((right.K.d s (s + 1)).val.app (op V) b))
  augmentation_pair : ∀ (V : X.Opens) (a : Γ(F, V)) (b : Γ(G, V)),
    pair 0 0 V ((left.augmentation.f 0).val.app (op V) a)
        ((right.augmentation.f 0).val.app (op V) b) =
      (target.augmentation.f 0).val.app (op V) (tmulSection a b)
```

The original module publicly imports ModuleCupResolutionData and retains the
original public ModuleCechComparison and WeilConjectures CechComparison exports.
Its IsModuleCupProduct definition and exists_unique_moduleCupProduct signature
stay verbatim. The new proof imports PairingExists and ResolutionInvariance
privately. Thus no consumer has a compiler error caused by this change and
there are no forced adaptations. This only changes the home module of existing
data declarations, not what they mean; no target semantics review is reopened.

## Users

The full downstream import closure from tools/downstream.py is listed, including
consumers without a textual reference. Existing source files are not adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupScalarComparison | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupUnitComparison | S3 | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1ProductInjective | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1ProductSpanning | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethCechModels | F4 | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohIso | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProductResidueH1Injective | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.CechCupProduct | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.CechCupPullbackCompat | Y2 | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Same public declarations and imports; no adaptation. |
| TargetsCheck | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Same public declarations and imports; no adaptation. |

## Status

landed 20261013T100051-L-2475276 2026-10-13 (merge of deliver/P3/Sheaf.Paper.ModuleCohomologyCupProduct)
