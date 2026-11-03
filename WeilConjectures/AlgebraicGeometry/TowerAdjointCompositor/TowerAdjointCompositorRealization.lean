/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
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
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSiteCoherence
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData

import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSiteCoherence
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.FiniteType
import WeilConjectures.AlgebraicGeometry.Finite.FiniteSiteWordRefinement
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportSiteCoherence
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections

/-! # Actual tower adjoint compositors

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/
`sk-prop-sp-composition-comparisons.proof.md`, (1)--(3)
(blueprint: lem-sp-tower-adjoint-compositor-realization).

The indices m,n denote positive exponents m+1,n+1. The full categories retain actual
ordinary derived-tower morphisms. The left arrow is the existing tower-calculus
composition arrow, and the right arrow is characterized by its composite counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u w
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

section Evaluation
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
open WeilConjectures.SemilinearSections
variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type w}
  [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
  [Category.{w} D₁] [Category.{w} D₂] [Category.{w} D₃]

end Evaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.ProEtale.TowerAdjointCompositor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- Package the given actual tower adjunction with its counit-preserving evaluations.
This adds no operations to the interfaces of det-sp-tower-gluing.
Source: blueprint comparisons (3) (blueprint: lem-sp-tower-adjoint-compositor-realization). -/
structure Pair {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) where
  closed : ∀ M : SpTowerCalculus.C l E b q X,
    spConstructibleTorTowers l E Y (q.abelian Y)
      ((SpTowerCalculus.F l E b o q c).obj M.obj)
  right : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X
  adj : SpTowerGluing.support l E b o q c closed ⊣ right
  levels : SpTowerGluing.Levels l E b o q c closed right adj

/-- The given restricted compact-support functor of a packaged adjunction.
Source: blueprint comparisons (3) (blueprint: lem-sp-tower-adjoint-compositor-realization). -/
abbrev left {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (P : Pair l E b o q c) := SpTowerGluing.support l E b o q c P.closed

/-- The specified finite coefficient counit mate, with no flatness assumption.
Source: blueprint comparisons (2),(3); det-sp-reduction-exceptional
(blueprint: lem-sp-tower-adjoint-compositor-realization). -/
def coefficient {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (P : Pair l E b o q c) {m n : ℕ} (h : m ≤ n)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)) :=
  SpTowerGluing.coefficientMate l E b c m n h
    (P.levels.finite_closed n) (P.levels.finite_closed m)
    (P.levels.scalarX m n h) (P.levels.scalarY m n h)
    (P.levels.right n) (P.levels.right m)
    (P.levels.adjunction n) (P.levels.adjunction m) K (P.levels.direct_image_iso m n h K)

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [QuasiCompact f] [QuasiCompact g]
  {cf : Compactification f} {cg : Compactification g} {ch : Compactification (f ≫ g)}

/-- The finite right compositor is the unique counit-preserving adjunction comparison.
The finite datum supplies the proper/open normalized alpha, while the right adjunctions
are precisely those specified by the tower evaluations.
Source: blueprint comparisons (1),(3)
(blueprint: lem-sp-tower-adjoint-compositor-realization). -/
def finiteTheta (Pf : Pair l E b o q cf) (Pg : Pair l E b o q cg)
    (Ph : Pair l E b o q ch)
    (A : ∀ n : ℕ, FiniteAdjointCompositorDatum (SpTowerShriek.R l E n) cf cg ch)
    (n : ℕ) : Ph.levels.right n ≅ Pg.levels.right n ⋙ Pf.levels.right n :=
  (Ph.levels.adjunction n).rightAdjointUniq
    (((Pf.levels.adjunction n).comp (Pg.levels.adjunction n)).ofNatIsoLeft (A n).alpha)

/-- Preservation of the normalized full subcategories by both members of the given
adjunction. The unnormalized uniform categories are already its source and target.
Source: blueprint comparisons (3) (blueprint: lem-sp-tower-adjoint-compositor-realization). -/
def PreservesNormalized {U V : Scheme.{u}} {h : U ⟶ V} {c : Compactification h}
    (P : Pair l E b o q c) : Prop :=
  (∀ M : SpTowerCalculus.C l E b q U,
    IsSpNormalizedTower l E U (q.abelian U) M.obj →
    IsSpNormalizedTower l E V (q.abelian V) ((left l E b o q P).obj M).obj) ∧
  (∀ K : SpTowerCalculus.C l E b q V,
    IsSpNormalizedTower l E V (q.abelian V) K.obj →
    IsSpNormalizedTower l E U (q.abelian U) (P.right.obj K).obj)

/-- Actual reduction equations for both image towers, conjugated only by the specified
finite evaluation identifications; in particular the right comparison is c_h itself.
Source: blueprint comparisons (3), actual reductions
(blueprint: lem-sp-tower-adjoint-compositor-realization). -/
structure Reductions {U V : Scheme.{u}} {h : U ⟶ V} {c : Compactification h}
    (P : Pair l E b o q c) : Prop where
  left : ∀ (m n : ℕ) (v : m ≤ n) (M : SpTowerCalculus.C l E b q U),
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E v) V).map
        ((P.levels.support_evaluation n).comparison.hom.app M.obj) ≫
      (reductionDirectImageComparison (SpTowerCalculus.quotient l E v) c.i c.g).app
        ((spDerivedCoefficientEvaluation l E U (q.abelian U) n).obj M.obj) ≫
      (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
        (SpTowerCalculus.reduction l E U (q.abelian U) v (q.scalar U v) M.obj) =
      SpTowerCalculus.reduction l E V (q.abelian V) v (q.scalar V v)
        ((left l E b o q P).obj M).obj ≫
      (P.levels.support_evaluation m).comparison.hom.app M.obj
  right : ∀ (m n : ℕ) (v : m ≤ n) (K : SpTowerCalculus.C l E b q V),
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E v) U).map
        ((P.levels.comparison n).hom.app K).hom ≫
      (coefficient l E b o q P v ((SpTowerGluing.level l E b q V n).obj K)).hom ≫
      ((P.levels.right m).map (ObjectProperty.homMk
        (SpTowerCalculus.reduction l E V (q.abelian V) v (q.scalar V v) K.obj))).hom =
      SpTowerCalculus.reduction l E U (q.abelian U) v (q.scalar U v) (P.right.obj K).obj ≫
        ((P.levels.comparison m).hom.app K).hom

/-- The reduction square for an actual natural transformation of tower functors.
The functors and the map are in ordinary derived-tower categories before evaluation.
Source: blueprint comparisons (3), two explicit squares
(blueprint: lem-sp-tower-adjoint-compositor-realization). -/
def ReductionSquare {U V : Scheme.{u}}
    {F G : SpTowerCalculus.C l E b q U ⥤ SpTowerCalculus.C l E b q V}
    (a : F ⟶ G) : Prop :=
  ∀ (m n : ℕ) (h : m ≤ n) (K : SpTowerCalculus.C l E b q U),
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) V).map
        ((spDerivedCoefficientEvaluation l E V (q.abelian V) n).map (a.app K).hom) ≫
      SpTowerCalculus.reduction l E V (q.abelian V) h (q.scalar V h) (G.obj K).obj =
    SpTowerCalculus.reduction l E V (q.abelian V) h (q.scalar V h) (F.obj K).obj ≫
      (spDerivedCoefficientEvaluation l E V (q.abelian V) m).map (a.app K).hom

/-- All comparisons, counits, finite evaluations and reduction squares of the node.
Source: blueprint comparisons (1)--(3)
(blueprint: lem-sp-tower-adjoint-compositor-realization). -/
structure Laws (k : Type u) [Field k]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (hP : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z hP)
    (Pf : Pair l E b o q cf) (Pg : Pair l E b o q cg) (Ph : Pair l E b o q ch)
    (A : ∀ n : ℕ, FiniteAdjointCompositorDatum (SpTowerShriek.R l E n) cf cg ch)
    (alpha : left l E b o q Pf ⋙ left l E b o q Pg ≅ left l E b o q Ph)
    (theta : Ph.right ≅ Pg.right ⋙ Pf.right) : Prop where
  proper_open : ∀ M : SpTowerCalculus.C l E b q X,
    (alpha.hom.app M).hom =
      (cal.composition.composition f g (f ≫ g) rfl cf cg ch).hom.app M
  counit : ∀ K : SpTowerCalculus.C l E b q Z,
    (left l E b o q Pf ⋙ left l E b o q Pg).map (theta.hom.app K) ≫
      (Pf.adj.comp Pg.adj).counit.app K = alpha.hom.app (Ph.right.obj K) ≫ Ph.adj.counit.app K
  unique : ∀ t : Ph.right ≅ Pg.right ⋙ Pf.right,
    (∀ K : SpTowerCalculus.C l E b q Z,
      (left l E b o q Pf ⋙ left l E b o q Pg).map (t.hom.app K) ≫
        (Pf.adj.comp Pg.adj).counit.app K =
      alpha.hom.app (Ph.right.obj K) ≫ Ph.adj.counit.app K) → t = theta
  composite_counit : ∀ K : SpTowerCalculus.C l E b q Z,
    (left l E b o q Pg).map (Pf.adj.counit.app (Pg.right.obj K)) ≫ Pg.adj.counit.app K =
      (Pf.adj.comp Pg.adj).counit.app K
  left_evaluation : ∀ (n : ℕ) (M : SpTowerCalculus.C l E b q X),
    (spDerivedCoefficientEvaluation l E Z (q.abelian Z) n).map (alpha.hom.app M).hom ≫
        (Ph.levels.support_evaluation n).comparison.hom.app M.obj =
      (Pg.levels.support_evaluation n).comparison.hom.app ((left l E b o q Pf).obj M).obj ≫
      (reductionCompactSupport (SpTowerShriek.R l E n) cg.i cg.g).map
        ((Pf.levels.support_evaluation n).comparison.hom.app M.obj) ≫
      ((A n).alpha.hom.app ((SpTowerGluing.level l E b q X n).obj M)).hom
  right_evaluation : ∀ (n : ℕ) (K : SpTowerCalculus.C l E b q Z),
    (SpTowerGluing.level l E b q X n).map (theta.hom.app K) ≫
        (Pf.levels.comparison n).hom.app (Pg.right.obj K) ≫
        (Pf.levels.right n).map ((Pg.levels.comparison n).hom.app K) =
      (Ph.levels.comparison n).hom.app K ≫
        (finiteTheta l E b o q Pf Pg Ph A n).hom.app ((SpTowerGluing.level l E b q Z n).obj K)
  normalized_f : PreservesNormalized l E b o q Pf
  normalized_g : PreservesNormalized l E b o q Pg
  normalized_gf : PreservesNormalized l E b o q Ph
  reductions_f : Reductions l E b o q Pf
  reductions_g : Reductions l E b o q Pg
  reductions_gf : Reductions l E b o q Ph
  left_square : ReductionSquare l E b q alpha.hom
  right_square : ReductionSquare l E b q theta.hom

end AlgebraicGeometry.ProEtale.TowerAdjointCompositor

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
