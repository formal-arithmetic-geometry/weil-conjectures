/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
import WeilConjectures.Compactification.CategoryBaseChange
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerTransitionCompatibility
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarRestriction
import WeilConjectures.AlgebraicGeometry.SmoothPurity.ChartNormalizedModelIdentification
import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.CompactificationRefinementCoherence
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportDomains
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenPasting
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Compactification.Dense
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateRightComparisons
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartAdmissibility
import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateCategories
import WeilConjectures.AlgebraicGeometry.SmoothOfRelativeDimension.SmoothAdmissibleCoordinateCover
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerBinaryPairGluing
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerPairOpenRestriction2
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerLocalCounitRepresentability
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1CoefficientCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1GeometricCoordinates

/-! # Tower orientation and smooth purity

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.md
(blueprint: det-sp-tower-gamma).

The existing map definitions and predicates are extracted verbatim to make them
available below the tower theorem without an import cycle
(blueprint: def-sp-tower-gamma-data).

All natural indices are predecessors of positive exponents. The section-preserving
realization changes coordinates in the ordinary derived category of strict towers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerGamma

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- The root-normalized shifted degree-one word, with the same finite root projection
as the coordinate construction. Source: clause (1) (blueprint: det-sp-tower-gamma). -/
def rootWord (T : Scheme.{u}) (w : SpChartAdmissibility.Twists l E T)
    (roots : SpCoordinateAdjunction.RootLines l E T) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    (hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (cc : SpTowerP1.CoefficientCoordinates l E n T hT) : SpTowerP1.LevelWord l E n T where
  tower := (SpCoordinateAdjunction.line l E w 1)⟦(2 : ℤ)⟧
  etale := (Etale.ordinaryFiniteLine (SpTowerP1.levelRing l E n) (l ^ (n + 1))
    (SpTowerP1.levelAnnihilates l E n) T)⟦(2 : ℤ)⟧
  comparison := (((SpTowerP1.nu l E n T).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      (SpTowerP1.nuSingle l E n T _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (cc.line ≪≫ (roots.iso n).symm ≪≫ (w.level n 1).symm) ≪≫
        (((SpTowerShriek.ev l E T n).mapDerivedCategorySingleFunctor 0).app _).symm) ≪≫
    (((SpTowerShriek.Ev l E T n).commShiftIso (2 : ℤ)).app _).symm).hom

/-- The given right-adjoint output in its retained ordinary etale origin, with the
specified finite adjunction comparison and exact evaluation factors.
Source: clauses (1)--(2), finite evaluations (blueprint: det-sp-tower-gamma). -/
def targetWord {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q c hF G adj) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    (K : SpTowerCalculus.C l E b q Y) : SpTowerP1.LevelWord l E n X where
  tower := (exceptional l E b q G).obj K
  etale := (lv.realization n).right.obj
    ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K))
  comparison := ((lv.realization n).rightIso.inv.app _ ≫
    ((lv.comparison n).inv.app K).hom) ≫
    (SpTowerCalculus.levelComparison l E b q X n).inv.app (G.obj K).obj

/-- The retained ordinary origin of a tower input, followed by its specified
section-preserving evaluation. Source: clause (2) (blueprint: det-sp-tower-gamma). -/
def inputWord {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q c hF G adj) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    (K : SpTowerCalculus.C l E b q Y) : SpTowerP1.LevelWord l E n Y where
  tower := (realization l E b q Y).obj K
  etale := (lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K)
  comparison := (lv.realization n).originIso.hom.app _ ≫
    (SpTowerCalculus.levelComparison l E b q Y n).inv.app K.obj

/-- Unique comparison of ordinary right adjoints, using the canonical compactification
comparison on the left. Thus it preserves the actual counit.
Source: clauses (1)--(2), finite adjunction identifications
(blueprint: det-sp-tower-gamma). -/
def finiteRightComparison (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (p : Z ⟶ Y) [IsProper p] [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (hF : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (G : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (adj : reductionCtfCompactSupport A j p hF ⊣ G)
    (r : ReductionExceptionalRealization A j p hF G adj) :
    r.right ≅ Etale.rightDerivedUpperShriek (ULift.{u + 1} A) (j ≫ p) :=
  r.adjunction.rightAdjointUniq
    ((Etale.rightDerivedUpperShriekAdjunction
      (ULift.{u + 1} A) (j ≫ p)).ofNatIsoLeft
        (Etale.rightDerivedLowerShriekIso (ULift.{u + 1} A) (factorization j p)).symm)

end AlgebraicGeometry.ProEtale.SpTowerGamma

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
