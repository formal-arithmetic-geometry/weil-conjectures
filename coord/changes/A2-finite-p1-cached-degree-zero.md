# ordinaryFiniteDegreeZero and ordinaryFiniteShiftedLinePullback

## Reason

The complete proof of the assigned twisted-unit base-change equation exceeded the per-file 60-second limit because concrete single-degree embeddings and their derived comparisons were repeatedly unfolded during kernel conversion. Naming the canonical functor before taking its object map, and naming the corresponding comparisons, shares the same constructed data. Both definition modules are unclaimed. No definition in WeilConjectures is changed.

## Old

```lean
def ordinaryFiniteDegreeZero (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) : DerivedCategoryModule A T :=
  (DerivedCategory.singleFunctor _ 0).obj F

def ordinaryFiniteShiftedLinePullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (ordinaryFinitePullback A f).obj
        ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) ≅
      (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧ :=
  letI : (ordinaryFinitePullback A f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  ((ordinaryFinitePullback A f).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (t.line f hY))
```

## New

```lean
def ordinaryFiniteSingleFunctor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ DerivedCategoryModule A T :=
  DerivedCategory.singleFunctor _ 0

theorem ordinaryFiniteSingleFunctor_eq (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    ordinaryFiniteSingleFunctor A T = DerivedCategory.singleFunctor _ 0 := rfl

def ordinaryFiniteDegreeZero (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) : DerivedCategoryModule A T :=
  (ordinaryFiniteSingleFunctor A T).obj F

def ordinaryFiniteSingleExactPullbackIso (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryFiniteSingleFunctor A Y ⋙
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ≅
      upperStar (ModuleCat.{u + 1} A) f ⋙ ordinaryFiniteSingleFunctor A X :=
  (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0

def ordinaryFiniteSinglePullbackIso (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryFiniteSingleFunctor A Y ⋙ ordinaryFinitePullback A f ≅
      upperStar (ModuleCat.{u + 1} A) f ⋙ ordinaryFiniteSingleFunctor A X :=
  Functor.isoWhiskerLeft (ordinaryFiniteSingleFunctor A Y)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
    ordinaryFiniteSingleExactPullbackIso A f

def ordinaryFiniteShiftedLinePullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (ordinaryFinitePullback A f).obj
        ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) ≅
      (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧ :=
  letI : (ordinaryFinitePullback A f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  ((ordinaryFinitePullback A f).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      ((ordinaryFiniteSinglePullbackIso A f).app _ ≪≫
        (ordinaryFiniteSingleFunctor A X).mapIso (t.line f hY))
```

The functor equation is proved by reflexivity. The exact comparison is the library comparison itself; the pullback comparison is its canonical composition with the exact/left-derived isomorphism. Unfolding the new definitions recovers the old arrows. Every existing signature, public import and attribute stays unchanged. No object is selected from an existence statement. These definitions occur downstream of targets, so their meaning is reopened for review; the new definitions are definitionally the same objects and maps.

## Users

The table records the whole-word declaration users returned by `tools/downstream.py --uses ordinaryFiniteDegreeZero ordinaryFiniteShiftedLinePullback`. Their occurrences were read: they use the same objects/maps, with the unchanged canonical degree-zero and shifted comparison formulas. All further users through ordinaryFiniteLine and the projective-line interfaces also see definitionally identical data.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.AffineLinearActionFamily` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.AffineLinearTraceAction` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.AffineTraceLineLocalization` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.AmbientAffineTranslationConstruction` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.FiniteP1ChernAdjunctBaseChange` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.FiniteP1ChernAdjunctMate` | X5 | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.FiniteP1ChernMapBaseChange` | X7 | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula` | F1 | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.FiniteP1KummerNaturality` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.FiniteP1KummerSplitting` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange` | A2 | Statement unchanged; original hole proved |
| `Sheaf.AlgebraicGeometry.FiniteTwistDerivedEvaluationPullback` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows` | unclaimed | Adapted here; canonical constructed data factored through cached functor |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer` | unclaimed | Adapted here; canonical constructed data factored through cached functor |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps` | Z9 | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Untwist` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalData` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.SfP1CoordinateIntegrals` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.SfP1IntegralTransport` | X6 | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.Paper.AffineLinePurityCoordinateMaps` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.Paper.AffineOrderedIntegrationTransposes` | J7 | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.Paper.EvenLineProductIntegrationMaps` | unclaimed | Private coefficient-generic helpers use the degree-zero interface; public signatures unchanged |
| `Sheaf.Paper.KummerAdditivity` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.Paper.OrientationEtaleFamily` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.Paper.P1KummerTraceSiteTransport` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.Paper.ProEtaleProjectiveLineTrace` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.Paper.SupportedProjectiveChern` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.Paper.TowerP1EtaleWords` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.Paper.TowerP1FormulaLevelComparisons` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.Paper.TwistedCoordinateSectionCoprojection` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.Paper.TwistedCoordinateSectionCore` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.Paper.VectorIntegrationSiteComparison` | P2 | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.SecSmoothPurity.TransportAffineTrace` | unclaimed | Definitionally identical objects and arrows; no statement changes |
| `Sheaf.SixFunctors.ProjectiveLineTraceModel` | unclaimed | Definitionally identical objects and arrows; no statement changes |

The original P1KummerTraceSiteTransport, GeoP1Cohomology and
OrdinaryFiniteP1KummerMaps consumers compile without adaptations. Their checks
exercise the old comparison and shift formulas against the factored definitions.

EvenLineProductIntegrationMaps originally fails at shiftedLine_ctf: its explicit
simp list unfolds ordinaryFiniteDegreeZero, leaving the new functor wrapper and
producing a mismatch against the native single-functor object. Adding that name
to the simp list compiles but reached 65 seconds during delivery. Instead, its
private ordinaryLine_ctf helper now states the same object through
ordinaryFiniteDegreeZero and explicitly unfolds that wrapper in its proof. A
proved private comparedLine_ctf applies the site-comparison constructibility
lemma for an arbitrary coefficient ring before specializing to Ring P.
shiftedLine_ctf then only unfolds shiftedLine and ordinaryFiniteLine. A private
proof import of OrdinaryFiniteP1Kummer provides this interface directly, and
local irreducibility of the cached embedding, shiftedLine, and the finite Tate
line keeps their constructed objects abstract during elaboration. The consumer
is unclaimed. All its public signatures, existing attributes, and definitions
are unchanged; the private helper's new statement is definitionally identical.
Each modified module passes its per-file compile check. Checked
consumer copies are excluded from the packet unless adapted.

## Status

landed 20261026T065000-L-2652866 2026-10-26 (merge of deliver/A2/Sheaf.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange)
