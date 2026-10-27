# ordinaryFiniteClass and the degree-zero realization

## Reason

The complete Chern-square proof exceeds the file limit during conversion of concrete
Ext/derived-morphism terms. Construct the degree-zero functor with its named degree-zero
object as the explicit object field; its maps and functor laws remain those of the canonical
single-degree embedding. Cache the canonical Ext equivalence against this functor and share
the realization formula on Ext representatives. The definitions contain constructed data,
with no existence witness or new mathematical assumption. Both definition modules and the
adapted arbitrary-base bijectivity consumer are unclaimed. No adopted source-library module
changes. Targets using these definitions are reopened for independent meaning review.

The shared X5 comparison repair landed during this session. This packet preserves its
ordinaryFiniteUnit body, public import of RelativeKummerExchangeGenerators, and public
interfaces. Its genericConstantIso value is now expressed by its identical cached single-degree
factorization in ordinaryFiniteUnitPullback. Conversion from the generic wrapper to that cached
interface took 98 seconds; constructing the same factors with shared endpoints avoids it. The complete main proof stays in its assigned module.

## Old

```lean
def ordinaryFiniteSingleFunctor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ DerivedCategoryModule A T :=
  DerivedCategory.singleFunctor _ 0

def ordinaryFiniteDegreeZero (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) : DerivedCategoryModule A T :=
  (ordinaryFiniteSingleFunctor A T).obj F

def ordinaryFiniteClassCore {C : Type*} {D : Type*}
    [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X : C} {Z : D} (e : Z ⟶ G.obj X) (Y : C) (n : ℕ)
    (c : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) :
    Ext.{u + 1} Z (G.obj Y) n :=
  (Ext.mk₀ e).comp ((Ext.homEquiv.symm c).mapExactFunctor G) (zero_add n)

def ordinaryFiniteClass (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (n : ℕ)
    (c : (DerivedCategory.singleFunctor _ 0).obj (ordinaryFiniteConstant A T) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj F)⟦(n : ℤ)⟧) :
    Sheaf.H ((moduleAbelianForget A T).obj F) n :=
  ordinaryFiniteClassCore (moduleAbelianForget A T)
    (ordinaryFiniteIntegralGenerator A T) F n c

instance ordinaryFiniteDegreeZero_isGE (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    DerivedCategory.TStructure.t.IsGE (ordinaryFiniteDegreeZero A T F) 0 := by
  unfold ordinaryFiniteDegreeZero
  rw [ordinaryFiniteSingleFunctor_eq]
  infer_instance

instance ordinaryFiniteDegreeZero_isLE (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    DerivedCategory.TStructure.t.IsLE (ordinaryFiniteDegreeZero A T F) 0 := by
  unfold ordinaryFiniteDegreeZero
  rw [ordinaryFiniteSingleFunctor_eq]
  infer_instance

def ordinaryFiniteP1KummerClass (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u})
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤))) :
    Sheaf.H ((moduleAbelianForget A (ProjectiveLine S)).obj
      (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA)) 2 :=
  Sheaf.H.map (ordinaryFiniteRootMap A N hA (ProjectiveLine S)) 2
    ((ProjectiveLine S).kummerδ₁ N hP
      (Scheme.Pic.toCohomologicalPicardGroup (ProjectiveLine S)
        (Scheme.Pic.ofIsInvertible (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1))))
```

```lean
def ordinaryFiniteUnitPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryFinitePullback A f).obj (ordinaryFiniteUnit A Y) ≅
      ordinaryFiniteUnit A X :=
  genericConstantIso (ModuleCat.{u + 1} A) (ModuleCat.of A A) f
```

## New

Both definition modules and the arbitrary-base consumer locally reuse the canonical
HasSheafify and IsGrothendieckAbelian proposition instances already stored in
DerivedCategoryModule. These local registrations export no instance.
The Kummer module also names the existing canonical derived localization before its
object projections are used. Its local instance registration unfolds to precisely
HasDerivedCategory.ofIsGrothendieckAbelian; no different localization is selected.

```lean
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
```

```lean
@[instance_reducible]
def ordinaryFiniteDerivedCategoryInstance (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

attribute [local instance 100000] ordinaryFiniteDerivedCategoryInstance
```

```lean
def ordinaryFiniteDegreeZero (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) : DerivedCategoryModule A T :=
  (DerivedCategory.singleFunctor _ 0).obj F

def ordinaryFiniteSingleFunctor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ DerivedCategoryModule A T :=
  { DerivedCategory.singleFunctor _ 0 with obj := ordinaryFiniteDegreeZero A T }

def ordinaryFiniteExtHomEquiv (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (M F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (n : ℕ) :
    Ext M F n ≃ ((ordinaryFiniteSingleFunctor A T).obj M ⟶
      ((ordinaryFiniteSingleFunctor A T).obj F)⟦(n : ℤ)⟧) :=
  by
    unfold ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
    exact Ext.homEquiv

def ordinaryFiniteExtClassCore {C : Type*} {D : Type*}
    [Category C] [Category D] [Abelian C] [Abelian D]
    [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X : C} {Z : D} (e : Z ⟶ G.obj X) (Y : C) (n : ℕ) (x : Ext X Y n) :
    Ext.{u + 1} Z (G.obj Y) n :=
  (Ext.mk₀ e).comp (x.mapExactFunctor G) (zero_add n)

def ordinaryFiniteClassCore {C : Type*} {D : Type*}
    [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X : C} {Z : D} (e : Z ⟶ G.obj X) (Y : C) (n : ℕ)
    (c : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) :
    Ext.{u + 1} Z (G.obj Y) n :=
  ordinaryFiniteExtClassCore G e Y n (Ext.homEquiv.symm c)

def ordinaryFiniteClass (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (n : ℕ)
    (c : (ordinaryFiniteSingleFunctor A T).obj (ordinaryFiniteConstant A T) ⟶
      ((ordinaryFiniteSingleFunctor A T).obj F)⟦(n : ℤ)⟧) :
    Sheaf.H ((moduleAbelianForget A T).obj F) n :=
  ordinaryFiniteExtClassCore (moduleAbelianForget A T)
    (ordinaryFiniteIntegralGenerator A T) F n
    ((ordinaryFiniteExtHomEquiv A T (ordinaryFiniteConstant A T) F n).symm c)

instance ordinaryFiniteDegreeZero_isGE (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    DerivedCategory.TStructure.t.IsGE (ordinaryFiniteDegreeZero A T F) 0 :=
  by
    unfold ordinaryFiniteDegreeZero
    infer_instance

instance ordinaryFiniteDegreeZero_isLE (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    DerivedCategory.TStructure.t.IsLE (ordinaryFiniteDegreeZero A T F) 0 :=
  by
    unfold ordinaryFiniteDegreeZero
    infer_instance

def ordinaryFiniteKummerClass (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (L : T.Pic) :
    Sheaf.H ((moduleAbelianForget A T).obj (Scheme.finiteEtaleTateLine T N A hA)) 2 :=
  Sheaf.H.map (ordinaryFiniteRootMap A N hA T) 2
    (T.kummerδ₁ N hT (Scheme.Pic.toCohomologicalPicardGroup T L))

def ordinaryFiniteP1PicardClass (S : Scheme.{u}) : (ProjectiveLine S).Pic :=
  Scheme.Pic.ofIsInvertible (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1)

def ordinaryFiniteP1KummerClass (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u})
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤))) :
    Sheaf.H ((moduleAbelianForget A (ProjectiveLine S)).obj
      (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA)) 2 :=
  ordinaryFiniteKummerClass A N hA (ProjectiveLine S) hP (ordinaryFiniteP1PicardClass S)
```

```lean
def ordinaryFiniteUnitPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryFinitePullback A f).obj (ordinaryFiniteUnit A Y) ≅
      ordinaryFiniteUnit A X :=
  (ordinaryFiniteSinglePullbackIso A f).app _ ≪≫
    (ordinaryFiniteSingleFunctor A X).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app (ModuleCat.of A A))
```

The existing ordinaryFiniteSingleFunctor_eq remains reflexivity. Complete proved
APIs expose ordinaryFiniteExtHomEquiv_eq, ordinaryFiniteClass_extHomEquiv and
ordinaryFiniteP1ChernSpec_iff. They identify the actual canonical equivalence, realization
formula and O(1) Kummer normalization.

The arrows module adds the proved equations ordinaryFiniteSingleExactPullbackIso_eq,
ordinaryFiniteUnitPullback_eq and ordinaryFiniteShiftedLinePullback_eq. The unit equation
unfolds to the same single-degree and constant-sheaf comparisons as genericConstantIso;
the other two are defining equations. All existing public imports stay intact.

The unclaimed OrdinaryFiniteClassArbitraryBase preserves its public statement and proof
argument. Its final bijectivity-composition line uses the cached equivalence:

```lean
  exact h.comp
    (ordinaryFiniteExtHomEquiv A T (ordinaryFiniteConstant A T) F n).symm.bijective
```

## Users

The table includes the current whole-word users reported by tools/downstream.py for
ordinaryFiniteDegreeZero, ordinaryFiniteSingleFunctor, ordinaryFiniteClassCore, ordinaryFiniteClass,
ordinaryFiniteP1KummerClass, ordinaryFiniteUnit, ordinaryFiniteLine and ordinaryFiniteUnitPullback.
Earlier users are retained as a conservative superset. Claim holders follow the current
72-hour project claim interval.

The table records the whole-word consumers from tools/downstream.py for the class,
constant unit, line, degree-zero embedding and unit comparison. It retains additional
inverse-image users checked while investigating the interface; that functor was restored
verbatim and is unchanged in this packet. Existing users see definitionally identical
constructed data. Unchanged consumer checks and any necessary adaptations are recorded
in report.md. The only currently adapted modules are the two unclaimed definition
modules and the assigned item.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.AffineLinearActionFamily` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.AffineLinearActionRigidity` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.AffineLinearTraceAction` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.AffineLinearUniversalAction` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.AffineTraceConstruction` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.AffineTraceLineCounitBaseChange` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.AffineTraceLineLocalization` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.AffineTraceLineOpenCounitBaseChange` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.AffineTraceRightNormalForm` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.AffineTraceTowerCounitBaseChange` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.AmbientAffineTranslationConstruction` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.BundleSectionComparisonIsoPasting` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.BundleSectionOrientationMapExt` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.BundleSectionProjectionUnit` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.BundleSectionPurityUnitIsIso` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.BundleSectionPurityUnitNormalization` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.BundleSectionRankZeroAffineNormalization` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.ChartSumAffineCounitTransport` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.Curve.FiniteEtaleCup` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.DerivedOpenCounitTensorAction` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.EtaleDegreeZeroHom` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.FiniteP1ChernAdjunctBaseChange` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.FiniteP1ChernAdjunctMate` | unclaimed | Proof import of UnitPullbackComp; actual-unit square from its proved composition equation; local canonical proposition instances and single-functor transparency; signatures unchanged |
| `Sheaf.AlgebraicGeometry.FiniteP1ChernMapBaseChange` | X7 | Original hole proved; statement unchanged |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalAlpha` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalChernComponents` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula` | F1 | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.FiniteP1KummerNaturality` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.FiniteP1KummerSplitting` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange` | unclaimed | Local single-functor transparency and reuse of the canonical proposition instances; signatures unchanged |
| `Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientationData` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.FiniteTwistDerivedEvaluationPullback` | A2 | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.GabberRegularPairPurity` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.NormalizedKummerCohomologyArrows` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrderedTateSectionPullback` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryAffineLineTensorCounit` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryAffineProjectionReassociation` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryAffineTensorActions` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryEtaleCup` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteClassComparison` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteClassInjectivity` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows` | unclaimed | Canonical interface aligned here |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DatumUniqueness` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalUnit` | Z8 | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer` | unclaimed | Canonical interface aligned here |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerBaseChange` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps` | unclaimed | Remove local registrations of eliminated auxiliary proofs _proof_14 and _proof_15; signatures unchanged |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Untwist` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteTraceCounit` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinarySupportedChernNormalization` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OriginClassProjectiveComparison` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OriginComparisonArrows` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OriginProjectiveNormalization` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.ProEtaleP1DiagonalComponents` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalData` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalTraceCalculation` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.ProjectiveLineTrace` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.RegularSupportedClassOperations` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison` | U3 | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.SfP1IntegralTraceComparison` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.SfP1IntegralTransport` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.SfP1IntegralTransportData` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.SpP1NormalizedFamilyCore` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.SupportedKummerLocalizationBoundary` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.VectorBundleIntegration` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocal` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.VectorIntegrationChartCoefficientZero` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.VectorIntegrationDirectSumLocal` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.VectorIntegrationIdentityUnit` | unclaimed | Use the cached comparison equations in the existing identity proof; local single-functor transparency; signatures unchanged |
| `Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility` | F3 | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.VectorIntegrationMate` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.VectorIntegrationRankZeroLocal` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.VectorIntegrationSwapChartPrefix` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.VectorIntegrationSwapLocal` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.VectorIntegrationTensorCounit` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.VectorTraceGeometricDescent` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineCoefficientCounitMaps` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineCoefficientCounitNormalization` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineCounitScalar` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineDiagonalIntegrationConstructions` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineDiagonalPowerCoefficient` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineDiagonalRawTransposePower` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineDiagonalTateCoordinates` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineDiagonalTensorCoordinates` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineDiagonalTraceRestriction` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineDiagonalTransposePower` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineLinePurityComparison` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineLinePurityCoordinateMaps` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineLinePuritySource` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineOrderedIntegrationData` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineOrderedIntegrationTransposes` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineSpacePurityComparison` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineSpaceThomMap` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineSpaceTraceFactorization` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineTowerIntegrationSiteTransport` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AffineTranslationTrace` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.BaseChangedLineTraceEvaluation` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.CartierDualKummerNormalization` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.ChartCounitScalarTransport` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.ChartDncVectorFactors` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.ChartGeometricCounitEvaluation` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.ChartTargetOpenDescent` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.CompositionModelOrientationDefinitions` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.CoordinateCounitArrows` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.CoordinateLineAdjunctionMaps` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.CoordinateLineCounitTensor` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.CoordinateProductPresentations` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.CoordinateSectionProjectiveTrace` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.CoordinateSectionTensorTrace` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.CoordinateTowerNormalizationData` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.DiagonalAffineTraceCoordinates` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.DiagonalAffineTraceSiteData` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.DiagonalCounitComparisonData` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.DiagonalDncChartNormalization` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.DiagonalExchangeNaturality` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.DiagonalOrdinaryChartLift` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.DiagonalOrdinaryOrientationNormalization` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.DiagonalOrdinaryOrientationRigidity` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.DiagonalOrientationChartExistence` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.DiagonalOrientationCharts` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.DiagonalOrientationChoiceIndependent` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.DiagonalOrientationCompatibility` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.DiagonalOrientationRefinementData` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.EvenLineProductIntegrationMaps` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FieldOrientationSystemComparison` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FieldOrientationSystemFiniteOrientation` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FieldPurityTransposeLevelWords` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteOrientationReduction` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteProductScalarPresentation` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteReductionLineChartScalars` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteReductionLineInputConstructible` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteRingSectionDeformation` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteSiteCoordinates` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteSiteTensorProjection` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteSmoothAdjunctionData` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteSmoothCoefficientArrows` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteSmoothLevelOfOrientation` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteSmoothPurityMaps` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteSmoothQuotientCoherence` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.FramedForgetSupport` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.IntegrationExponentTransposeTransport` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.KummerAdditivity` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.NormalizedCartierForget` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.NormalizedSmoothOrientationUnits` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.OrderedAffineTraceNormalForm` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.OrderedAffineTransposeData` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.OrderedIntegrationComparison` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.OrderedTateScalarNormalization` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.OrderedTowerOrientation` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.OrientationEtaleFamily` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.P1CounitScalar` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.P1KummerChernScalar` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.P1KummerDerivedScalar` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.P1KummerScalarEndpointComposition` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.P1KummerScalarEndpoints` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.P1KummerTraceSiteTransport` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.P1SplittingScalar` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.ProEtaleCtfPullbackDomains` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.ProEtaleOrderedIntegration` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.ProEtaleProjectiveCoefficient` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.ProEtaleProjectiveLineTrace` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.ProEtaleVectorIntegration` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.ProjectionUnitIntegration` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.PurityCompositionComparisons` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.PurityDiagonalDualizingData` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.PurityOrientationDatum` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.PurityTensorMapNaturality` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.RamifiedCartierSupportedPurity` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.RamifiedRootLimitTorsionUnit` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.RegularImmersionPurityComparison` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.SectionCoordinateCounitNormalization` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.SmoothPurityCompositionFactors` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.SmoothPurityTowerGammaData` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.SmoothTrace` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.TensorTransposeFiniteEvaluation` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.TowerOrientationEvaluation` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.TowerP1CoefficientCoordinates` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.TowerP1EtaleDelta` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.TowerP1EtaleOperations` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.TowerP1KernelScalarData` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.TowerTensorTransposeEvaluation` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.TowerTensorTransposeWords` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.TwistedCoordinateSectionCoprojection` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.TwistedCoordinateSectionCore` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.TwistedCoordinateSectionMaps` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.TwistedCoordinateSectionNormalization` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.TwistedCoordinateSectionOrdinary` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.TwistedPullbackTowerDomainDefinitions` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.UniversalTranslationMultiplier` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.VectorFrameIntegrationSiteDescent` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.VectorIntegrationChartComparison` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.VectorIntegrationChartCoordinates` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.VectorIntegrationSiteComparison` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.VectorIntegrationUnitTranspose` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.VectorModelChartDescent` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.VectorPurityNormalization` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.VectorTensorSiteEquations` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.VectorTraceScalarDescent` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Paper.VectorZeroSectionIntegrationBaseChange` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SecSmoothPurity.DncCoefficientTransportData` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingData` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SecSmoothPurity.FiniteSmoothDualizingScalar` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SecSmoothPurity.NestedAffineChartFormulas` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SecSmoothPurity.NestedAffineFormulaData` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SecSmoothPurity.ReductionExceptionalObjects` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SecSmoothPurity.TransportAffineNormalization` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SecSmoothPurity.TransportAffineTrace` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SecSmoothPurity.TransportFiniteLineDerived` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SixFunctors.AffineDualizingCoefficient` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SixFunctors.ProjectiveLineExceptionalBaseChange` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SixFunctors.ProjectiveLineTraceAdjunction` | D3 | Definitionally identical data; no statement change |
| `Sheaf.SixFunctors.ProjectiveLineTraceCounitBaseChange` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SixFunctors.ProjectiveLineTraceModel` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.Targets.VectorBundlePurity` | unclaimed | Definitionally identical data; no statement change |

| `Sheaf.AlgebraicGeometry.OrdinaryFiniteAdjunctScalarFaithfulness` | unclaimed | Remove local registrations of eliminated auxiliary proofs _proof_14 and _proof_15; signatures unchanged |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteClassScalarFaithfulness` | unclaimed | Unfold the factored Ext helper at the two existing realization unfold steps; signatures unchanged |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteFibreHomologyComparison` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteGeometricPointHomology` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1FibreHomologyCard` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.ProjectiveLineTateCoefficientGenerator` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.SfP1ChartExchange` | E2 | Proof adaptation needed (red build 2026-10-26T15:17Z, 4445 importers quarantined): it kept ordinaryFiniteSingleFunctor locally irreducible, so its object map no longer reduced to ordinaryFiniteDegreeZero. Fixed by the maintainer in d70ab261005. |
| `Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransport` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransportFalse` | Q4 | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransportTrue` | R1 | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.VectorIntegrationCartesianPrefix` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.VectorIntegrationOverlapChartPrefix` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.AlgebraicGeometry.VectorIntegrationRestrictedChartTransport` | unclaimed | Definitionally identical data; no statement change |
| `Sheaf.SixFunctors.ProjectiveLinePresentedTraceExchange` | C3 | Definitionally identical data; no statement change |

## Consumer repairs

All adapted consumers are currently unclaimed. The original consumer checks against the
changed definitions produced these errors, before the listed proof repairs:

- FiniteP1TwistedUnitBaseChange: at line 164, the cached single comparison had source
  G.obj K where the goal used ordinaryFiniteDegreeZero K. The local irreducible declaration
  for G prevented its explicit object field from being recognized. Expose only that cached
  functor locally; share the canonical proposition instances to avoid repeated conversion.
- OrdinaryFiniteClassScalarFaithfulness: at line 69, rewriting Ext.mapExactFunctor_comp
  found no occurrence because ordinaryFiniteExtClassCore now names that expression.
  Unfold that definition alongside ordinaryFiniteClassCore at the two existing unfold steps.
- VectorIntegrationIdentityUnit: at line 99, exact_identity_single found no occurrence of
  mapDerivedCategorySingleFunctor because the canonical comparison was cached. Rewrite by
  the complete comparison equations in the existing simplification; no argument is changed.
- FiniteP1ChernAdjunctMate: the original file stopped after 120 seconds at the equality
  identifying the cached unit comparison with genericConstantIso. The existing proved
  ordinaryFiniteUnitPullback_comp gives the square for the actual cached unit comparisons
  directly. Use this existing equation and retain the original formal mate argument; remove
  the now-unused private generic-constant helpers and their proof imports. This compiles in
  13.5 seconds with profiling enabled, compared with 90 seconds for the conversion proof.
- OrdinaryFiniteAdjunctScalarFaithfulness: line 38 referred to the no-longer-generated
  ordinaryFinitePullback._proof_14. The sharing of canonical instance proofs removes both
  _proof_14 and _proof_15; remove only their local registrations.
  OrdinaryFiniteP1KummerMaps produced the identical unknown-constant error at line 65 and
  receives exactly the same two-registration repair.

## Status

landed 20261026T142458-L-330646 2026-10-26 (merge of deliver/X7/Sheaf.AlgebraicGeometry.FiniteP1ChernMapBaseChange)
