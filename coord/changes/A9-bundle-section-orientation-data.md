# Finite-ring bundle section orientation data

## Reason

Move the eighteen canonical definitions and instances verbatim into a publicly re-exported
data module so the affine-normalization and equality-detection lemmas can refer to them
without importing the theorem they reduce. This is a mathematical dependency extraction.
All four original theorem signatures are unchanged. No source-library declaration is edited.
The data is still explicitly constructed from the same pullback, coefficient, projection,
and adjunction maps; no witness is chosen from a new existence theorem.

## Old

The following declarations occurred in
`lean/Sheaf/AlgebraicGeometry/FiniteRingBundleSectionOrientation.lean`:

```lean
/-- Bundle affineness from the recorded geometry, used to synthesize compactifications.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
instance bundleSectionAffine (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    IsAffineHom (VectorBundleZeroSection.π S d M) :=
  (vectorIntegration_geometry S d M).1
/-- The bundle is of finite type locally, as recorded in its integration construction.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
instance bundleSectionFiniteType (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    LocallyOfFiniteType (VectorBundleZeroSection.π S d M) :=
  (vectorIntegration_geometry S d M).2.1
/-- The total space is Noetherian, including the empty and rank-zero cases.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
instance bundleSectionNoetherian (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    IsNoetherian (VectorBundleZeroSection.scheme S d M) :=
  (vectorIntegration_geometry S d M).2.2
/-- Every open of the Noetherian base is Noetherian; overlaps need not be affine.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
instance bundleSectionOpenNoetherian (S : Scheme.{u}) [IsNoetherian S] (V : S.Opens) :
    IsNoetherian V.toScheme :=
  letI : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  { toIsLocallyNoetherian := inferInstance
    toCompactSpace :=
      { isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ } }
/-- The actual dualizing object for the chosen bundle compact-support adjunction.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionOmega (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    DerivedCategoryModule A (VectorBundleZeroSection.scheme S d M) :=
  (rightDerivedUpperShriek (ModuleCat.{u + 1} A)
    (VectorBundleZeroSection.π S d M)).obj (ordinaryFiniteUnit A S)
/-- The object z^* omega_pi on the ordinary unbounded category of the base.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionObject (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] : DerivedCategoryModule A S :=
  (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).obj
    (bundleSectionOmega A S d M)
/-- Canonical z^* pi^* A_S(d)[2d] = A_S(d)[2d], using pi z = 1.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionCoefficientIso (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).obj
        (vectorIntegrationCoefficient A N hA S d M) ≅
      affineLinearBaseCoefficient A N hA S d :=
  (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (VectorBundleZeroSection.zero S d M) (VectorBundleZeroSection.π S d M)
    (VectorBundleZeroSection.zero_spec S d M).1).app _
/-- Inverse images around a commuting square of sections, with their canonical compositors.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionPullbackSquare (A : Type (u + 1)) [CommRing A]
    {X U S T : Scheme.{u}} (z : S ⟶ X) (w : T ⟶ U) (h : U ⟶ X) (v : T ⟶ S)
    (hw : w ≫ h = v ≫ z) (K : DerivedCategoryModule A X) :
    (ordinaryFinitePullback A v).obj ((ordinaryFinitePullback A z).obj K) ≅
      (ordinaryFinitePullback A w).obj ((ordinaryFinitePullback A h).obj K) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v z).symm.app K ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w h (v ≫ z) hw.symm).app K
/-- The counit-preserving comparison on section objects: the canonical exceptional mate
of inverse compact-support exchange, followed by the constant-unit pullback comparison.
For the open and isomorphism squares below this is exactly the right-adjoint comparison.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U S T : Scheme.{u}} (p : X ⟶ S) (q : U ⟶ T)
    [HasCompactification p] [HasCompactification q] [QuasiCompact q]
    (h : U ⟶ X) (v : T ⟶ S) (sq : IsPullback h q p v)
    (z : S ⟶ X) (w : T ⟶ U) (hw : w ≫ h = v ≫ z) :
    (ordinaryFinitePullback A v).obj
        ((ordinaryFinitePullback A z).obj
          ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) p).obj
            (ordinaryFiniteUnit A S))) ⟶
      (ordinaryFinitePullback A w).obj
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) q).obj
          (ordinaryFiniteUnit A T)) :=
  (bundleSectionPullbackSquare A z w h v hw _).hom ≫
    (ordinaryFinitePullback A w).map
      ((rightDerivedUpperShriekBaseChangeMap A sq).app (ordinaryFiniteUnit A S) ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} A) q).map
          (ordinaryFiniteUnitPullback A v).hom)
/-- The zero section expressed in the actual inverse frame, by its Cartesian lifting property.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionChartZero (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d M V) :
    V.toScheme ⟶ affineTraceTower V.toScheme d :=
  (vectorIntegrationChart_isPullback S d M V e).lift
    (V.ι ≫ VectorBundleZeroSection.zero S d M) (𝟙 _)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f ↦ V.ι ≫ f) (VectorBundleZeroSection.zero_spec S d M).1).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
/-- Canonical comparison from a restricted global section object to the frame section object.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionChartComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d M V) :=
  bundleSectionComparison A (VectorBundleZeroSection.π S d M)
    (affineTraceProjection V.toScheme d) (vectorIntegrationChart S d M V e) V.ι
    (vectorIntegrationChart_isPullback S d M V e) (VectorBundleZeroSection.zero S d M)
    (bundleSectionChartZero S d M V e)
    ((vectorIntegrationChart_isPullback S d M V e).lift_fst _ _ _)
/-- The actual affine adjunct alpha_p, not an arbitrary purity isomorphism.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionAffineAdjunct (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
    (affineTraceProjection T d)).homEquiv _ (ordinaryFiniteUnit A T)
      ((affineLinearCompactComparison N hN A hA T hT d).inv ≫
        affineTraceCounit A N hA t D T hT d)
/-- The coefficient identification along the zero section in a frame.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionChartCoefficient (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d M V) :
    (ordinaryFinitePullback A (bundleSectionChartZero S d M V e)).obj
        ((affineTraceRight A N hA V.toScheme d).obj (ordinaryFiniteUnit A V.toScheme)) ≅
      affineLinearBaseCoefficient A N hA V.toScheme d :=
  (ordinaryFinitePullback A (bundleSectionChartZero S d M V e)).mapIso
      (affineLinearCoefficientDescent A N hA t V.toScheme
        (affineTracePullbackInvertible N V.ι hS) d) ≪≫
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (bundleSectionChartZero S d M V e) (affineTraceProjection V.toScheme d)
      ((vectorIntegrationChart_isPullback S d M V e).lift_snd _ _ _)).app _
/-- Every affine frame has the specified inverse-affine-adjunct orientation. Using an
inverse equation avoids assuming in advance the invertibility that the theorem asserts.
Since every frame, not a selected cover, occurs, this also states agreement on overlaps
and under every invertible linear change of frames via the same restriction map.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def BundleSectionOrientationNormalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (o : bundleSectionObject A S d M ≅ affineLinearBaseCoefficient A N hA S d) : Prop :=
  ∀ (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (V : S.Opens) (_hV : IsAffine V.toScheme)
    (e : VectorBundleZeroSection.Trivialization S d M V),
    (ordinaryFinitePullback A V.ι).map o.inv ≫
        bundleSectionChartComparison A S d M V e =
      (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d).hom ≫
        (bundleSectionChartCoefficient N A hA t S hS d M V e).inv ≫
        (ordinaryFinitePullback A (bundleSectionChartZero S d M V e)).map
          (bundleSectionAffineAdjunct N hN A hA t D V.toScheme
            (affineTracePullbackInvertible N V.ι hS) d)
/-- Canonical rank-zero comparison with the identity adjunction, under E = S.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionRankZeroComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S]
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank 0]
    (e : VectorBundleZeroSection.scheme S 0 M ≅ S)
    (hz : e.inv = VectorBundleZeroSection.zero S 0 M) :
    bundleSectionObject A S 0 M ⟶ ordinaryFiniteUnit A S :=
  letI : IsIso (VectorBundleZeroSection.zero S 0 M) := hz ▸ inferInstance
  (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).inv.app _ ≫
    bundleSectionComparison A (VectorBundleZeroSection.π S 0 M) (𝟙 S)
      (VectorBundleZeroSection.zero S 0 M) (𝟙 S)
      (IsPullback.of_horiz_isIso
        (CommSq.mk ((VectorBundleZeroSection.zero_spec S 0 M).1.trans
          (Category.comp_id _).symm)))
      (VectorBundleZeroSection.zero S 0 M) (𝟙 S) rfl ≫
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.app _ ≫
    ((conjugateIsoEquiv
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) (𝟙 S))
      (Adjunction.id)) (unboundedEtaleLowerShriekId A S).symm).hom.app _
/-- The canonical tensor-unit identification pi^* A_S tensor A_E(d)[2d] = A_E(d)[2d].
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionPurityUnitIso (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    vectorBundlePurityTwistedPullback A N hA S d M (ordinaryFiniteUnit A S) ≅
      vectorIntegrationCoefficient A N hA S d M :=
  ((derivedTensor (ModuleCat.{u + 1} A) (VectorBundleZeroSection.scheme S d M)).mapIso
    (ordinaryFiniteUnitPullback A (VectorBundleZeroSection.π S d M))).app _ ≪≫
      derivedTensorLeftUnitor (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.scheme S d M) _
/-- The actual purity adjunct at the coefficient unit, with the specified projection map.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionPurityUnitMap (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (p : (vectorBundlePurityLower A S d M).obj
        (vectorBundlePurityTwistedPullback A N hA S d M (ordinaryFiniteUnit A S)) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) S).obj (ordinaryFiniteUnit A S)).obj
        (vectorIntegrationSource A N hA S d M)) :
    vectorIntegrationCoefficient A N hA S d M ⟶ bundleSectionOmega A S d M :=
  (bundleSectionPurityUnitIso N A hA S d M).inv ≫
    (vectorBundlePurityAdjunction A S d M).homEquiv _ (ordinaryFiniteUnit A S)
      (p.hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) S).obj (ordinaryFiniteUnit A S)).map
          (vectorBundleIntegration N hN A hA S hS d M) ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} A) S (ordinaryFiniteUnit A S)).hom)
/-- Equality with inverse integration-normalized purity, written without inverse maps
whose invertibility would have to be assumed. The projection inverse p is characterized
by p.inv being the canonical projection map; the remaining equation is on o.inv.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def BundleSectionPurityCompatibility (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (o : bundleSectionObject A S d M ≅ affineLinearBaseCoefficient A N hA S d) : Prop :=
  ∃ p : (vectorBundlePurityLower A S d M).obj
        (vectorBundlePurityTwistedPullback A N hA S d M (ordinaryFiniteUnit A S)) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) S).obj (ordinaryFiniteUnit A S)).obj
        (vectorIntegrationSource A N hA S d M),
    p.inv = vectorBundlePurityProjectionMap A N hA S d M (ordinaryFiniteUnit A S) ∧
    o.inv = (bundleSectionCoefficientIso A N hA S d M).inv ≫
      (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).map
        (bundleSectionPurityUnitMap N hN A hA S hS d M p)

```

## New

The declarations displayed above are byte-for-byte identical in
`lean/Sheaf/AlgebraicGeometry/FiniteRingBundleSectionOrientationData.lean`.
The original module publicly imports that module:

```lean
public import Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientationData
```

The original public imports remain available through the data module, and the Noetherian
scheme import is public there because its public open-scheme instance uses that interface.
Unused private proof imports have been removed. Definition meanings, universes, instance
priorities and declaration visibility are preserved, so no target-meaning review is reopened.

## Users

`tools/downstream.py` reports the following transitive importers. Its `--uses` audit of
all eighteen moved names finds just `Sheaf.Paper.FiniteRingSectionDeformation` beyond the
original module: its `purityUnitSource` and `purityUnitMate` abbreviations call the unchanged
`bundleSectionPurityUnitIso` and `bundleSectionPurityUnitMap`. Both remain available through
the same public import. Every other importer has no direct reference to a moved name.
No consumer source edit is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.AffineCounitScalar | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.ChartCounitScalarTransport | T8 | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.ChartDncVectorFactors | S9 | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.ChartExceptionalMateCoherence | W3 | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.CondensedTateIntegralTower | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.CondensedTateIntegralTowerData | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FinitePuritySourceUnitReduction | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteRingSectionDeformation | M7 | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteTateBalancedScalarPullback | H2 | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteTateScalarSourceNormalization | G3 | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.GeneralChartComparisons | G6 | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.NormalizedTateTensorTower | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.OrderedTateScalarNormalization | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.P1CounitScalar | F4 | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.RawChartScalarCounitPasting | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.SmoothPurityTowerGamma | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Paper.VectorTraceScalarDescent | S8 | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Public re-export preserves declarations and definitions; no edit. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | A9 | Item module re-exports unchanged definitions and proves two theorems from the new lemmas. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientationData | A9 | Uses or supplies the extracted unchanged canonical data. |
| Sheaf.AlgebraicGeometry.BundleSectionPurityUnitIsIso | A9 | Uses or supplies the extracted unchanged canonical data. |
| Sheaf.AlgebraicGeometry.BundleSectionPurityUnitNormalization | A9 | Uses or supplies the extracted unchanged canonical data. |
| Sheaf.AlgebraicGeometry.BundleSectionOrientationMapExt | A9 | Uses or supplies the extracted unchanged canonical data. |

## Status

landed 20261025T100811-L-3625154 2026-10-25 (merge of deliver/A9/Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation)
