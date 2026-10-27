# FiniteRingSectionDeformation canonical coefficient units and aliases

## Reason

The original bundle adjunct and unit purity mate repeatedly compare the derived tensor unit
with the constant coefficient sheaf in degree zero. These objects are definitionally equal,
but reducing their monoidal and derived-category constructions made full-file compiles
exceed 60 seconds. Write the existing ordinaryFiniteUnit explicitly, use the existing
coordinate transpose and unit purity maps, and make duplicate functor names abbreviations.
The geometric objects, integration map, compactification, adjunction and canonical maps
are preserved. No theorem hypothesis or conclusion is weakened. The five library targets
are unchanged. Their definitions still denote the same derived-category objects and maps.

The unit identification has identity inverse by singleFunctorObjUnitIso_inv. Consequently
its hom is also identity by Iso.hom_inv_id. Removing these identity factors preserves the
maps. The unit coefficient isomorphism differs only by the same identity factor inside
mapIso. CoordinateCounitArrows.towerAdjoint is the original affineAdjoint body verbatim.
The bundle right adjoint is the same functor with the same geometry instances.

## Old

```lean
def affineAdjoint (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) ⟶
      dualizingComplex (ModuleCat.{u + 1} A) (affineTraceProjection S d) :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
    (affineTraceProjection S d)).homEquiv _ _
      ((affineLinearCompactComparison N hN A hA S hS d).inv ≫
        affineTraceCounit A N hA t D S hS d ≫
          (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S).hom)
```

```lean
def bundleRight (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    DerivedCategoryModule A S ⥤
      DerivedCategoryModule A (VectorBundleZeroSection.scheme S d M) :=
  letI := (vectorIntegration_geometry S d M).1
  letI := (vectorIntegration_geometry S d M).2.1
  rightDerivedUpperShriek (ModuleCat.{u + 1} A) (VectorBundleZeroSection.π S d M)
```

```lean
def bundleAdjoint (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    vectorIntegrationCoefficient A N hA S d M ⟶
      (bundleRight A S d M).obj (𝟙_ _) :=
  (vectorBundlePurityAdjunction A S d M).homEquiv _ _
    (vectorBundleIntegration N hN A hA S hS d M ≫
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S).hom)
```

```lean
def bundleSectionAdjoint (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    affineLinearBaseCoefficient A N hA S d ⟶
      (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).obj
        ((bundleRight A S d M).obj (𝟙_ _)) :=
  (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (VectorBundleZeroSection.zero S d M) (VectorBundleZeroSection.π S d M)
    (VectorBundleZeroSection.zero_spec S d M).1).inv.app _ ≫
      (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).map
        (bundleAdjoint N hN A hA S hS d M)
```

```lean
def bundleOrientation (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).obj
        ((bundleRight A S d M).obj (𝟙_ _)) ≅
      affineLinearBaseCoefficient A N hA S d :=
  letI := (bundleAdjoint_isIso N hN A hA S hS d M).2
  (asIso (bundleSectionAdjoint N hN A hA S hS d M)).symm
```

```lean
def bundleFrameSectionMap (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] (W : S.Opens)
    [IsNoetherian W.toScheme]
    (e : VectorBundleZeroSection.Trivialization S d M W) :
    (ordinaryFinitePullback A W.ι).obj
      ((ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).obj
        ((bundleRight A S d M).obj (𝟙_ _))) ⟶
      sectionInvariant A (affineTraceProjection W.toScheme d) (standardZero W.toScheme d) :=
  letI := (vectorIntegration_geometry S d M).1
  letI := (vectorIntegration_geometry S d M).2.1
  sectionMap A (VectorBundleZeroSection.π S d M) (affineTraceProjection W.toScheme d)
    W.ι (vectorIntegrationChart S d M W e) (vectorIntegrationChart_isPullback S d M W e)
    (VectorBundleZeroSection.zero S d M) (standardZero W.toScheme d)
    (bundleFrame_zero S d M W e)
```

```lean
def purityUnitCoefficientIso (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    vectorBundlePurityTwistedPullback A N hA S d M (ordinaryFiniteUnit A S) ≅
      vectorIntegrationCoefficient A N hA S d M :=
  ((derivedTensor (ModuleCat.{u + 1} A) (VectorBundleZeroSection.scheme S d M)).mapIso
    (ordinaryFiniteUnitPullback A (VectorBundleZeroSection.π S d M) ≪≫
      singleFunctorObjUnitIso (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.scheme S d M))).app _ ≪≫
    derivedTensorLeftUnitor (ModuleCat.{u + 1} A) _ _
```

```lean
def purityUnitMate (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (p : (vectorBundlePurityLower A S d M).obj
        (vectorBundlePurityTwistedPullback A N hA S d M (ordinaryFiniteUnit A S)) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) S).obj (ordinaryFiniteUnit A S)).obj
        (vectorIntegrationSource A N hA S d M)) :
    vectorIntegrationCoefficient A N hA S d M ⟶
      (bundleRight A S d M).obj (𝟙_ _) :=
  (purityUnitCoefficientIso A N hA S d M).inv ≫
    (vectorBundlePurityAdjunction A S d M).homEquiv _ _
      (p.hom ≫ ((derivedTensor (ModuleCat.{u + 1} A) S).obj
        (ordinaryFiniteUnit A S)).map (vectorBundleIntegration N hN A hA S hS d M) ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) S (ordinaryFiniteUnit A S)).hom) ≫
    (bundleRight A S d M).map
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S).hom
```

## New

```lean
abbrev affineAdjoint (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) ⟶
      dualizingComplex (ModuleCat.{u + 1} A) (affineTraceProjection S d) :=
  CoordinateCounitArrows.towerAdjoint N hN A hA t D S hS d
```

```lean
abbrev bundleRight (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    DerivedCategoryModule A S ⥤
      DerivedCategoryModule A (VectorBundleZeroSection.scheme S d M) :=
  letI := (vectorIntegration_geometry S d M).1
  letI := (vectorIntegration_geometry S d M).2.1
  rightDerivedUpperShriek (ModuleCat.{u + 1} A) (VectorBundleZeroSection.π S d M)
```

```lean
def bundleAdjoint (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    vectorIntegrationCoefficient A N hA S d M ⟶
      (bundleRight A S d M).obj (ordinaryFiniteUnit A S) :=
  (vectorBundlePurityAdjunction A S d M).homEquiv
    (vectorIntegrationCoefficient A N hA S d M) (ordinaryFiniteUnit A S)
    (vectorBundleIntegration N hN A hA S hS d M)
```

```lean
def bundleSectionAdjoint (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    affineLinearBaseCoefficient A N hA S d ⟶
      (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).obj
        ((bundleRight A S d M).obj (ordinaryFiniteUnit A S)) :=
  (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (VectorBundleZeroSection.zero S d M) (VectorBundleZeroSection.π S d M)
    (VectorBundleZeroSection.zero_spec S d M).1).inv.app _ ≫
      (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).map
        (bundleAdjoint N hN A hA S hS d M)
```

```lean
def bundleOrientation (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).obj
        ((bundleRight A S d M).obj (ordinaryFiniteUnit A S)) ≅
      affineLinearBaseCoefficient A N hA S d :=
  letI := (bundleAdjoint_isIso N hN A hA S hS d M).2
  (asIso (bundleSectionAdjoint N hN A hA S hS d M)).symm
```

```lean
def bundleFrameSectionMap (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] (W : S.Opens)
    [IsNoetherian W.toScheme]
    (e : VectorBundleZeroSection.Trivialization S d M W) :
    (ordinaryFinitePullback A W.ι).obj
      ((ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).obj
        ((bundleRight A S d M).obj (ordinaryFiniteUnit A S))) ⟶
      sectionInvariant A (affineTraceProjection W.toScheme d) (standardZero W.toScheme d) :=
  letI := (vectorIntegration_geometry S d M).1
  letI := (vectorIntegration_geometry S d M).2.1
  sectionMap A (VectorBundleZeroSection.π S d M) (affineTraceProjection W.toScheme d)
    W.ι (vectorIntegrationChart S d M W e) (vectorIntegrationChart_isPullback S d M W e)
    (VectorBundleZeroSection.zero S d M) (standardZero W.toScheme d)
    (bundleFrame_zero S d M W e)
```

```lean
abbrev purityUnitCoefficientIso (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    vectorBundlePurityTwistedPullback A N hA S d M (ordinaryFiniteUnit A S) ≅
      vectorIntegrationCoefficient A N hA S d M :=
  bundleSectionPurityUnitIso N A hA S d M
```

```lean
abbrev purityUnitMate (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (p : (vectorBundlePurityLower A S d M).obj
        (vectorBundlePurityTwistedPullback A N hA S d M (ordinaryFiniteUnit A S)) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) S).obj (ordinaryFiniteUnit A S)).obj
        (vectorIntegrationSource A N hA S d M)) :
    vectorIntegrationCoefficient A N hA S d M ⟶
      (bundleRight A S d M).obj (ordinaryFiniteUnit A S) :=
  bundleSectionPurityUnitMap N hN A hA S hS d M p
```

The new public imports provide definitions used in these aliases:
Sheaf.Paper.CoordinateCounitArrows and
Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation.

## Users

The downstream list was obtained with tools/downstream.py on 2026-10-24. The changed names occur in AmbientDiagonalPurityBaseChange, ChartDncVectorFactors,
FiniteSmoothPurityMaps and FiniteSmoothAdjunctionGeneralBase. Other rows are transitive
consumers. No consumer is edited.
All displayed coefficient unit replacements are definitionally equal to the old objects.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteRingSectionDeformation | F2 | canonical definitions adjusted as above |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | same canonical unit and map; direct consumer |
| Sheaf.Paper.CondensedTateIntegralTower | F4 | transitive consumer; no statement or proof edit |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | transitive consumer; no statement or proof edit |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | same canonical unit and map; direct consumer |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | transitive consumer; no statement or proof edit |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | transitive consumer; no statement or proof edit |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | transitive consumer; no statement or proof edit |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | same canonical unit and map; direct consumer |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | transitive consumer; no statement or proof edit |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | transitive consumer; no statement or proof edit |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | transitive consumer; no statement or proof edit |
| Sheaf.Paper.FiniteTateBalancedScalarPullback | Y2 | transitive consumer; no statement or proof edit |
| Sheaf.Paper.FiniteTateScalarSourceNormalization | C9 | transitive consumer; no statement or proof edit |
| Sheaf.Paper.VectorTraceScalarDescent | unclaimed | transitive consumer; no statement or proof edit |
| Sheaf.Paper.ChartCounitScalarTransport | unclaimed | transitive consumer; no statement or proof edit |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed | same canonical unit and map; direct consumer |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | transitive consumer; no statement or proof edit |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | transitive consumer; no statement or proof edit |
| Sheaf.Paper.OrderedTateScalarNormalization | unclaimed | transitive consumer; no statement or proof edit |
| Sheaf.Paper.P1CounitScalar | unclaimed | transitive consumer; no statement or proof edit |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | transitive consumer; no statement or proof edit |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | transitive consumer; no statement or proof edit |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | transitive consumer; no statement or proof edit |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | transitive consumer; no statement or proof edit |

FiniteSmoothPurityMaps and FiniteSmoothAdjunctionGeneralBase compiled unchanged against
the revised module. The current direct-importer list is also checked before delivery.
No forced adaptation is required.

## Status

landed 20261024T185148-L-3452986 2026-10-24 (merge of deliver/F2/Sheaf.Paper.FiniteRingSectionDeformation)
