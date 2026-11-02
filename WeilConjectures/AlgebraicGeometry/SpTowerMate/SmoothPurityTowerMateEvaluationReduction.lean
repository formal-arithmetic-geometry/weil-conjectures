/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
public import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Predicate
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.Compactification.CategoryBaseChange
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerTransitionCompatibility
public import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
public import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarRestriction
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.ChartNormalizedModelIdentification
public import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.CompactificationRefinementCoherence
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
public import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportDomains
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenPasting
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
public import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateRightComparisons
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartAdmissibility
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
public import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateCategories
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangleData
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
public import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
public import WeilConjectures.Algebra.Homology.OpenCoverMateComplexShortExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
public import WeilConjectures.Algebra.Homology.SubterminalLocal.SubterminalModuleLocalCalculus
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.ProEtaleRingedOpenCoverReflectsIso
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation
public import WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
public import WeilConjectures.SixFunctors.Supporting.PullbackTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.MixedBaseChangeOperations
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionCtfFunctors
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
public import WeilConjectures.AlgebraicGeometry.MixedBaseChangeInput
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportUniformTorBound
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor

/-! # Evaluation and reduction of the actual tower exceptional base-change mate

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-tower.proof.md, paragraphs (1)--(2)
(blueprint: lem-sp-tower-mate-evaluation-reduction).

Index n denotes the positive exponent n+1. All categories are the existing ordinary,
unnormalized, uniformly constructible finite-Tor tower categories. Coordinate changes
below use the supplied section-normalized equivalences and their units and counits.
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerMate

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- Cancel only the middle realization equivalence in a composite of actual operations.
Source: paragraph (1), coordinate transport (blueprint: lem-sp-tower-mate-evaluation-reduction).
-/
def composition {X Y Z : Scheme.{u}} (F : SpTowerShriek.D l E X ⥤ SpTowerShriek.D l E Y)
    (H : SpTowerShriek.D l E Y ⥤ SpTowerShriek.D l E Z) :
    ((SpTowerCalculus.realization l E b X (q.abelian X)).functor ⋙ F ⋙
        (SpTowerCalculus.realization l E b Y (q.abelian Y)).inverse) ⋙
      ((SpTowerCalculus.realization l E b Y (q.abelian Y)).functor ⋙ H ⋙
        (SpTowerCalculus.realization l E b Z (q.abelian Z)).inverse) ≅
    (SpTowerCalculus.realization l E b X (q.abelian X)).functor ⋙ F ⋙ H ⋙
      (SpTowerCalculus.realization l E b Z (q.abelian Z)).inverse :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      ((SpTowerCalculus.realization l E b Y (q.abelian Y)).invFunIdAssoc _))

/-- The actual compactification exchange transported to the original strict towers.
Source: paragraph (1) (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def exchange (x : SpTowerShriek.OpenExchange l E b o)
    {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {v : Y' ⟶ Y} (sq : IsPullback u' f' f v) (c : Compactification f) :
    SpTowerCalculus.F l E b o q c ⋙ SpTowerCalculus.etalePullback l E b o q v ⟶
      SpTowerCalculus.etalePullback l E b o q u' ⋙
        SpTowerCalculus.F l E b o q (c.ofIsPullback sq) :=
  (composition l E b q (SpTowerShriek.F l E b o c)
      (SpTowerShriek.pull l E b (o.geometry v))).hom ≫
    Functor.whiskerLeft _ (Functor.whiskerRight (SpTowerShriek.exchange l E b o x sq c) _) ≫
    (Functor.isoWhiskerLeft _ (Functor.associator _ _ _)).hom ≫
    (composition l E b q (SpTowerShriek.pull l E b (o.geometry u'))
      (SpTowerShriek.F l E b o (c.ofIsPullback sq))).inv

/-- Exact evaluation of tower pullback, with the given ordinary section normalization.
Source: paragraph (2), evaluation (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def pullEvaluation {U T : Scheme.{u}} (h : U ⟶ T) (n : ℕ) :
    SpTowerCalculus.etalePullback l E b o q h ⋙
        spDerivedCoefficientEvaluation l E U (q.abelian U) n ≅
      spDerivedCoefficientEvaluation l E T (q.abelian T) n ⋙
        proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) h :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (SpTowerCalculus.levelComparison l E b q U n).symm ≪≫
        (SpTowerCalculus.realization l E b U (q.abelian U)).invFunIdAssoc _)) ≪≫
    Functor.isoWhiskerLeft _ ((o.geometry h).pullEvaluation n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (SpTowerCalculus.levelComparison l E b q T n) _

/-- Membership certificates for restricting the given operations, together with the
actual right adjoints and their counit/unit-normalized finite comparisons. These are
outputs of the theorem, not extra geometric hypotheses.
Source: paragraphs (1)--(2) (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
structure Data {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {v : Y' ⟶ Y} (sq : IsPullback u' f' f v) (c : Compactification f) where
  support_closed : ∀ M : SpTowerCalculus.C l E b q X,
    spConstructibleTorTowers l E Y (q.abelian Y)
      ((SpTowerCalculus.F l E b o q c).obj M.obj)
  support_closed' : ∀ M : SpTowerCalculus.C l E b q X',
    spConstructibleTorTowers l E Y' (q.abelian Y')
      ((SpTowerCalculus.F l E b o q (c.ofIsPullback sq)).obj M.obj)
  pull_closed : ∀ M : SpTowerCalculus.C l E b q X,
    spConstructibleTorTowers l E X' (q.abelian X')
      ((SpTowerCalculus.etalePullback l E b o q u').obj M.obj)
  pull_closed' : ∀ K : SpTowerCalculus.C l E b q Y,
    spConstructibleTorTowers l E Y' (q.abelian Y')
      ((SpTowerCalculus.etalePullback l E b o q v).obj K.obj)
  finite_pull : ∀ (n : ℕ) (M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n)),
    spFiniteConstructibleTor X' (SpTowerShriek.R l E n)
      ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) u').obj M.obj)
  finite_pull' : ∀ (n : ℕ) (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)),
    spFiniteConstructibleTor Y' (SpTowerShriek.R l E n)
      ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) v).obj K.obj)
  right : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X
  right' : SpTowerCalculus.C l E b q Y' ⥤ SpTowerCalculus.C l E b q X'
  adjunction : SpTowerGluing.support l E b o q c support_closed ⊣ right
  adjunction' : SpTowerGluing.support l E b o q (c.ofIsPullback sq) support_closed' ⊣ right'
  levels : SpTowerGluing.Levels l E b o q c support_closed right adjunction
  levels' : SpTowerGluing.Levels l E b o q (c.ofIsPullback sq) support_closed' right' adjunction'

variable {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {v : Y' ⟶ Y} {sq : IsPullback u' f' f v} {c : Compactification f}
  (a : Data l E b o q sq c)

/-- Restrict the actual pullback to the full tower category on the left side.
Source: paragraph (1) (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def U : SpTowerCalculus.C l E b q X ⥤ SpTowerCalculus.C l E b q X' :=
  ObjectProperty.lift _
    (SpTowerCalculus.inclusion l E b q X ⋙ SpTowerCalculus.etalePullback l E b o q u')
    a.pull_closed

/-- Restrict the actual pullback on the base.
Source: paragraph (1) (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def V : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q Y' :=
  ObjectProperty.lift _
    (SpTowerCalculus.inclusion l E b q Y ⋙ SpTowerCalculus.etalePullback l E b o q v)
    a.pull_closed'

/-- The specified compactification exchange on full uniformly bounded ctf categories.
Source: paragraph (1) (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def beta (x : SpTowerShriek.OpenExchange l E b o) :
    SpTowerGluing.support l E b o q c a.support_closed ⋙ V l E b o q a ⟶
      U l E b o q a ⋙ SpTowerGluing.support l E b o q (c.ofIsPullback sq) a.support_closed' where
  app M := ObjectProperty.homMk ((exchange l E b o q x sq c).app M.obj)
  naturality _M _N t := ObjectProperty.hom_ext _ ((exchange l E b o q x sq c).naturality t.hom)

/-- The actual adjoint transpose as a natural transformation of tower functors.
Source: paragraph (2), e = eta followed by G'(beta inverse followed by v*counit)
(blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def mate (x : SpTowerShriek.OpenExchange l E b o) (hb : IsIso (beta l E b o q a x)) :
    a.right ⋙ U l E b o q a ⟶ V l E b o q a ⋙ a.right' :=
  (mateEquiv a.adjunction a.adjunction'
    (TwoSquare.mk _ _ _ _ (@inv _ _ _ _ (beta l E b o q a x) hb))).natTrans

/-- The finite source functor u_n^* G_n.
Source: paragraph (2) (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def finiteP (n : ℕ) :=
  a.levels.right n ⋙ mixedCtfPullback (SpTowerShriek.R l E n) u' (a.finite_pull n)

/-- The finite target functor G'_n v_n^*.
Source: paragraph (2) (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def finiteQ (n : ℕ) :=
  mixedCtfPullback (SpTowerShriek.R l E n) v (a.finite_pull' n) ⋙ a.levels'.right n

/-- The actual finite compactification exchange, using the canonical pullback identification.
Source: paragraphs (1)--(2) (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def finiteExchange (n : ℕ) :=
  mixedCompactSupportExchange (SpTowerShriek.R l E n)
    (ChosenCartesianSquare.mk sq.toCommSq sq.isoPullback
      sq.isoPullback_hom_fst sq.isoPullback_hom_snd) c

/-- The finite transpose, with the finite exchange fixed by its compactification formula.
Source: paragraph (2) (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def finiteMate (n : ℕ) (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n))
    (hb : IsIso ((finiteExchange l E b (sq := sq) (c := c) n).app
      ((a.levels.right n).obj K).obj)) :
    (finiteP l E b o q a n).obj K ⟶ (finiteQ l E b o q a n).obj K :=
  (a.levels'.adjunction n).homEquiv _ _ (ObjectProperty.homMk
    (@inv _ _ _ _ ((finiteExchange l E b (sq := sq) (c := c) n).app
      ((a.levels.right n).obj K).obj) hb ≫
      (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) v).map
        ((a.levels.adjunction n).counit.app K).hom))

/-- Evaluation of P, by actual pullback evaluation then the supplied gluing comparison.
Source: paragraph (2) (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def sourceComparison (n : ℕ) (K : SpTowerCalculus.C l E b q Y) :
    (spDerivedCoefficientEvaluation l E X' (q.abelian X') n).obj
        ((U l E b o q a).obj (a.right.obj K)).obj ≅
      ((finiteP l E b o q a n).obj ((SpTowerGluing.level l E b q Y n).obj K)).obj :=
  (pullEvaluation l E b o q u' n).app (a.right.obj K).obj ≪≫
    (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) u').mapIso
      ((spFiniteConstructibleTor X (SpTowerShriek.R l E n)).ι.mapIso
        ((a.levels.comparison n).app K))

/-- Evaluation of Q, by the supplied gluing comparison then actual pullback evaluation.
Source: paragraph (2) (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def targetComparison (n : ℕ) (K : SpTowerCalculus.C l E b q Y) :
    (spDerivedCoefficientEvaluation l E X' (q.abelian X') n).obj
        (a.right'.obj ((V l E b o q a).obj K)).obj ≅
      ((finiteQ l E b o q a n).obj ((SpTowerGluing.level l E b q Y n).obj K)).obj :=
  (spFiniteConstructibleTor X' (SpTowerShriek.R l E n)).ι.mapIso
      ((a.levels'.comparison n).app ((V l E b o q a).obj K)) ≪≫
    (spFiniteConstructibleTor X' (SpTowerShriek.R l E n)).ι.mapIso
      ((a.levels'.right n).mapIso (ObjectProperty.isoMk _
        ((pullEvaluation l E b o q v n).app K.obj)))

/-- The specified coefficient counit mate for f, using the gluing adjunctions.
Source: paragraph (2), c^f (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def coefficient (m n : ℕ) (h : m ≤ n)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)) :=
  SpTowerGluing.coefficientMate l E b c m n h
    (a.levels.finite_closed n) (a.levels.finite_closed m)
    (a.levels.scalarX m n h) (a.levels.scalarY m n h)
    (a.levels.right n) (a.levels.right m)
    (a.levels.adjunction n) (a.levels.adjunction m) K (a.levels.direct_image_iso m n h K)

/-- The source coefficient map, with the canonical scalar/pullback identification.
Source: paragraph (2), u_m^*c^f (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def sourceCoefficient (m n : ℕ) (h : m ≤ n)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)) :
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X').obj
        ((finiteP l E b o q a n).obj K).obj ⟶
      ((finiteP l E b o q a m).obj
        ((reductionCtfScalar (SpTowerCalculus.quotient l E h) Y
          (a.levels.scalarY m n h)).obj K)).obj :=
  (directImageScalarPullbackIso (SpTowerCalculus.quotient l E h) u').inv.app
      ((a.levels.right n).obj K).obj ≫
    (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E m) u').map
      (coefficient l E b o q a m n h K).hom

/-- The target coefficient map, including the scalar/pullback identification on the input.
Source: paragraph (2), c^{f'} (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def targetCoefficient (m n : ℕ) (h : m ≤ n)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)) :
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X').obj
        ((finiteQ l E b o q a n).obj K).obj ⟶
      ((finiteQ l E b o q a m).obj
        ((reductionCtfScalar (SpTowerCalculus.quotient l E h) Y
          (a.levels.scalarY m n h)).obj K)).obj :=
  (SpTowerGluing.coefficientMate l E b (c.ofIsPullback sq) m n h
    (a.levels'.finite_closed n) (a.levels'.finite_closed m)
    (a.levels'.scalarX m n h) (a.levels'.scalarY m n h)
    (a.levels'.right n) (a.levels'.right m)
    (a.levels'.adjunction n) (a.levels'.adjunction m)
    ((mixedCtfPullback (SpTowerShriek.R l E n) v (a.finite_pull' n)).obj K)
    (a.levels'.direct_image_iso m n h _)).hom ≫
  ((a.levels'.right m).map (ObjectProperty.homMk
    ((directImageScalarPullbackIso (SpTowerCalculus.quotient l E h) v).inv.app K.obj))).hom

/-- The actual input tower reduction as a morphism of finite full subcategories.
Source: paragraph (2), r^K (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def inputReduction (m n : ℕ) (h : m ≤ n) (K : SpTowerCalculus.C l E b q Y) :
    (reductionCtfScalar (SpTowerCalculus.quotient l E h) Y
        (a.levels.scalarY m n h)).obj ((SpTowerGluing.level l E b q Y n).obj K) ⟶
      (SpTowerGluing.level l E b q Y m).obj K :=
  ObjectProperty.homMk
    (SpTowerCalculus.reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj)

/-- The reduction of P in the finite source coordinates.
Source: paragraph (2), r^P (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def sourceReduction (m n : ℕ) (h : m ≤ n) (K : SpTowerCalculus.C l E b q Y) :=
  (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X').map
      (sourceComparison l E b o q a n K).inv ≫
    SpTowerCalculus.reduction l E X' (q.abelian X') h (q.scalar X' h)
      ((U l E b o q a).obj (a.right.obj K)).obj ≫
    (sourceComparison l E b o q a m K).hom

/-- The reduction of Q in the finite target coordinates.
Source: paragraph (2), r^Q (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
def targetReduction (m n : ℕ) (h : m ≤ n) (K : SpTowerCalculus.C l E b q Y) :=
  (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X').map
      (targetComparison l E b o q a n K).inv ≫
    SpTowerCalculus.reduction l E X' (q.abelian X') h (q.scalar X' h)
      (a.right'.obj ((V l E b o q a).obj K)).obj ≫
    (targetComparison l E b o q a m K).hom

/-- All identities for the specified tower mate, in the fixed finite coordinates.
The three reductions in the chain are actual reductions of the constructed tower maps.
Source: paragraphs (1)--(2) (blueprint: lem-sp-tower-mate-evaluation-reduction). -/
structure Laws (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (beta l E b o q a x))
    (hfinite : ∀ (n : ℕ) (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)),
      IsIso ((finiteExchange l E b (sq := sq) (c := c) n).app
        ((a.levels.right n).obj K).obj)) : Prop where
  exchange_evaluation : ∀ (n : ℕ) (M : SpTowerCalculus.C l E b q X),
    (spDerivedCoefficientEvaluation l E Y' (q.abelian Y') n).map
        ((beta l E b o q a x).app M).hom ≫
      (a.levels'.support_evaluation n).comparison.hom.app ((U l E b o q a).obj M).obj =
    (pullEvaluation l E b o q v n).hom.app
        ((SpTowerGluing.support l E b o q c a.support_closed).obj M).obj ≫
      (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) v).map
        ((a.levels.support_evaluation n).comparison.hom.app M.obj) ≫
      (finiteExchange l E b (sq := sq) (c := c) n).app
        ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj M.obj) ≫
      (reductionCompactSupport (SpTowerShriek.R l E n)
        (c.ofIsPullback sq).i (c.ofIsPullback sq).g).map
          ((pullEvaluation l E b o q u' n).inv.app M.obj)
  transpose : ∀ K : SpTowerCalculus.C l E b q Y,
    (mate l E b o q a x hb).app K =
      a.adjunction'.unit.app ((U l E b o q a).obj (a.right.obj K)) ≫
        a.right'.map ((@inv _ _ _ _ (beta l E b o q a x) hb).app (a.right.obj K) ≫
          (V l E b o q a).map (a.adjunction.counit.app K))
  evaluation : ∀ (n : ℕ) (K : SpTowerCalculus.C l E b q Y),
    (spDerivedCoefficientEvaluation l E X' (q.abelian X') n).map
        ((mate l E b o q a x hb).app K).hom ≫
      (targetComparison l E b o q a n K).hom =
    (sourceComparison l E b o q a n K).hom ≫
      (finiteMate l E b o q a n ((SpTowerGluing.level l E b q Y n).obj K)
        (hfinite n _)).hom
  source_reduction : ∀ (m n : ℕ) (h : m ≤ n) (K : SpTowerCalculus.C l E b q Y),
    sourceReduction l E b o q a m n h K =
      sourceCoefficient l E b o q a m n h ((SpTowerGluing.level l E b q Y n).obj K) ≫
        ((finiteP l E b o q a m).map (inputReduction l E b o q a m n h K)).hom
  target_reduction : ∀ (m n : ℕ) (h : m ≤ n) (K : SpTowerCalculus.C l E b q Y),
    targetReduction l E b o q a m n h K =
      targetCoefficient l E b o q a m n h ((SpTowerGluing.level l E b q Y n).obj K) ≫
        ((finiteQ l E b o q a m).map (inputReduction l E b o q a m n h K)).hom
  mixed : ∀ (m n : ℕ) (h : m ≤ n)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)),
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X').map
        (finiteMate l E b o q a n K (hfinite n K)).hom ≫
      targetCoefficient l E b o q a m n h K =
    sourceCoefficient l E b o q a m n h K ≫
      (finiteMate l E b o q a m
        ((reductionCtfScalar (SpTowerCalculus.quotient l E h) Y
          (a.levels.scalarY m n h)).obj K) (hfinite m _)).hom
  reduction_chain : ∀ (m n : ℕ) (h : m ≤ n) (K : SpTowerCalculus.C l E b q Y),
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X').map
        (finiteMate l E b o q a n ((SpTowerGluing.level l E b q Y n).obj K)
          (hfinite n _)).hom ≫ targetReduction l E b o q a m n h K =
      sourceCoefficient l E b o q a m n h ((SpTowerGluing.level l E b q Y n).obj K) ≫
        (finiteMate l E b o q a m
          ((reductionCtfScalar (SpTowerCalculus.quotient l E h) Y
            (a.levels.scalarY m n h)).obj ((SpTowerGluing.level l E b q Y n).obj K))
          (hfinite m _)).hom ≫
        ((finiteQ l E b o q a m).map (inputReduction l E b o q a m n h K)).hom ∧
    sourceCoefficient l E b o q a m n h ((SpTowerGluing.level l E b q Y n).obj K) ≫
        (finiteMate l E b o q a m
          ((reductionCtfScalar (SpTowerCalculus.quotient l E h) Y
            (a.levels.scalarY m n h)).obj ((SpTowerGluing.level l E b q Y n).obj K))
          (hfinite m _)).hom ≫
        ((finiteQ l E b o q a m).map (inputReduction l E b o q a m n h K)).hom =
      sourceCoefficient l E b o q a m n h ((SpTowerGluing.level l E b q Y n).obj K) ≫
        ((finiteP l E b o q a m).map (inputReduction l E b o q a m n h K)).hom ≫
        (finiteMate l E b o q a m ((SpTowerGluing.level l E b q Y m).obj K)
          (hfinite m _)).hom ∧
    sourceCoefficient l E b o q a m n h ((SpTowerGluing.level l E b q Y n).obj K) ≫
        ((finiteP l E b o q a m).map (inputReduction l E b o q a m n h K)).hom ≫
        (finiteMate l E b o q a m ((SpTowerGluing.level l E b q Y m).obj K)
          (hfinite m _)).hom =
      sourceReduction l E b o q a m n h K ≫
        (finiteMate l E b o q a m ((SpTowerGluing.level l E b q Y m).obj K)
          (hfinite m _)).hom

end AlgebraicGeometry.ProEtale.SpTowerMate

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
