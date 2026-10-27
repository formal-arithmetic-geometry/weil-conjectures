/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.Paper.PurityTowerReductionComparisons
import Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation
import Sheaf.AlgebraicGeometry.SmoothTensorDuality
import Sheaf.Paper.PurityPullbackReductionTransport
import Sheaf.Paper.PurityFiniteReductionTransport
import Sheaf.Paper.PurityPullbackLevelBounds
import Sheaf.AlgebraicGeometry.IntrinsicTorAmplitudeTransport

/-! # Finite purity conjugates actual exceptional tower reductions

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md, (3)
(blueprint: lem-sp-purity-conjugates-tower-reduction).

Indices are predecessors of positive exponents: level n has coefficients O_E/ell^(n+1).
Only the explicit word constructions from SmoothPurityTowerGamma are used; its tower
purity theorem and its normalized-tower conclusions are not used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpPurityReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  [b : SpTowerShriek.Base l E] (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

private theorem tensorWord_isIso (n : ℕ) (T : Scheme.{u})
    (tc : SpTowerP1.TensorCoordinates l E n b T)
    (A B : SpTowerP1.LevelWord l E n T)
    [IsIso A.comparison] [IsIso B.comparison] :
    IsIso (SpTowerP1.tensorWord l E n b tc A B).comparison := by
  have : IsIso (Prod.mkHom A.comparison B.comparison) :=
    (Iso.prod (asIso A.comparison) (asIso B.comparison)).isIso_hom
  dsimp only [SpTowerP1.tensorWord]
  infer_instance

private theorem coefficientWord_isIso (n : ℕ) (T : Scheme.{u})
    (w : SpChartAdmissibility.Twists l E T)
    (roots : SpCoordinateAdjunction.RootLines l E T)
    (units : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (cc : SpTowerP1.CoefficientCoordinates l E n T units)
    (tc : SpTowerP1.TensorCoordinates l E n b T) :
    ∀ d : ℕ, IsIso (SpTowerGamma.lineWord l E b T w roots n units cc tc d)
  | 0 => by
    exact (SpTowerP1.nuSingle l E n T _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso cc.unit ≪≫
      (((SpTowerShriek.ev l E T n).mapDerivedCategorySingleFunctor 0).app _).symm).isIso_hom
  | d + 1 => by
    have := coefficientWord_isIso n T w roots units cc tc d
    have : IsIso (SpTowerGamma.rootWord l E T w roots n units cc).comparison := by
      dsimp only [SpTowerGamma.rootWord]
      infer_instance
    exact tensorWord_isIso l E n T tc
      ⟨_, _, SpTowerGamma.lineWord l E b T w roots n units cc tc d⟩
      (SpTowerGamma.rootWord l E T w roots n units cc)

private theorem sourceComparison_isIso
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (w : SpChartAdmissibility.Twists l E X) (d : ℕ)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q c hF G adj)
    (roots : SpCoordinateAdjunction.RootLines l E X)
    (units : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤)))
    (cc : ∀ n : ℕ, SpTowerP1.CoefficientCoordinates l E n X (units n))
    (tc : ∀ n : ℕ, SpTowerP1.TensorCoordinates l E n b X)
    (gc : ∀ n : ℕ, SpTowerP1.GeometricCoordinates l E n f)
    (n : ℕ) (K : SpTowerCalculus.C l E b q Y) :
    IsIso (sourceComparison l E o q c w d hF G adj lv roots units cc tc gc n K) := by
  have : IsIso (SpTowerGamma.inputWord l E b o q c hF G adj lv n K).comparison := by
    dsimp only [SpTowerGamma.inputWord]
    infer_instance
  have : IsIso (SpTowerP1.pullWord l E n b (o.geometry f) (gc n)
      (SpTowerGamma.inputWord l E b o q c hF G adj lv n K)).comparison := by
    dsimp only [SpTowerP1.pullWord]
    infer_instance
  have : IsIso (SpTowerGamma.coefficientWord l E b X w roots n
      (units n) (cc n) (tc n) d).comparison :=
    coefficientWord_isIso l E n X w roots (units n) (cc n) (tc n) d
  have := tensorWord_isIso l E n X (tc n)
    (SpTowerP1.pullWord l E n b (o.geometry f) (gc n)
      (SpTowerGamma.inputWord l E b o q c hF G adj lv n K))
    (SpTowerGamma.coefficientWord l E b X w roots n (units n) (cc n) (tc n) d)
  dsimp only [sourceComparison, sourceWord]
  infer_instance

private theorem tor_cohomology (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (K : proEtaleDerivedCategory T A) (a z : ℤ)
    (ht : HasProEtaleTorAmplitude T A K a z) :
    ∀ i : ℤ, (i < a ∨ z < i) →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K) := by
  let F := finiteCoefficientIntrinsicRealization T A
  have : F.IsEquivalence := (finiteCoefficientIntrinsicRealization_exact T A).1
  let J := F.mapDerivedCategory.objPreimage K
  let e : F.mapDerivedCategory.obj J ≅ K := F.mapDerivedCategory.objObjPreimageIso K
  have ht' : HasProEtaleTorAmplitude T A (F.mapDerivedCategory.obj J) a z := by
    refine ⟨ht.1, ?_⟩
    intro L P hL f hf hP M i hi
    obtain ⟨eL⟩ := hL
    exact ht.2 L P ⟨eL ≪≫ e⟩ f hf hP M i hi
  have hf := (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn A T a z ht.1 J).mp ht'
  have hc := DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hf
  intro i hi
  have hz : IsZero ((DerivedCategory.homologyFunctor _ i).obj J) := by
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff J a).mp hc.1 i hi
    · exact (DerivedCategory.isLE_iff J z).mp hc.2 i hi
  exact (F.isZero_homologyFunctor_mapDerivedCategory_obj hz).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e).symm

/-- The unnormalized twisted pullback belongs to the uniform constructible finite-Tor
category, with both asserted intervals.
Source: gamma proof (3) (blueprint: lem-sp-purity-conjugates-tower-reduction).
Proof: smoothness and Noetherian quasi-compactness make f finite type. Apply
lem-sf-pullback-tor-amplitude at e(n+1). Twist preserves constructibility and the
Tor interval by prop-weil-twist-preserves. The shift [2d] replaces degree i by i+2d,
so its Tor bounds are [a-2d,b-2d]. Test against the coefficient unit in degree zero
to obtain the same cohomological bounds. These bounds and level constructibility
are exactly the defining conditions of sk-def-sp-normalized-towers' full category;
the separate normalization predicate is not imposed. -/
theorem pullbackTower_bounds
    (D : FiniteFieldDatum.{u}) [CharP D.k D.p] (hne : l ≠ D.p)
    {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [(j ≫ p).IsOver (Spec (.of D.k))]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]
    (w : SpChartAdmissibility.Twists l E X)
    (K : SpTowerCalculus.C l E b q Y) :
    spConstructibleTorTowers l E X (q.abelian X)
      (pullbackTower l E o q (j ≫ p) w d K) ∧
    ∀ a z : ℤ, a ≤ z →
      (∀ n : ℕ, HasProEtaleTorAmplitude Y (SpTowerShriek.R l E n)
        ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj K.obj) a z) →
      ∀ n : ℕ,
        SpTowerCalculus.cohomologicalInterval l E X n
          ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj
            (pullbackTower l E o q (j ≫ p) w d K)) (a - 2 * d) (z - 2 * d) ∧
        HasProEtaleTorAmplitude X (SpTowerShriek.R l E n)
          ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj
            (pullbackTower l E o q (j ≫ p) w d K)) (a - 2 * d) (z - 2 * d) := by
  have level (n : ℕ) (a z : ℤ) (haz : a ≤ z)
      (ht : HasProEtaleTorAmplitude Y (SpTowerShriek.R l E n)
        ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj K.obj) a z) :=
    pullback_level_bounds l E o q D hne (j ≫ p) d w K.obj n (K.property.1 n) a z haz ht
  obtain ⟨a, z, c, t, _, hct, hb⟩ := K.property.2
  constructor
  · refine ⟨fun n ↦ ⟨⟨c - 2 * d, t - 2 * d, sub_le_sub_right hct _,
          tor_cohomology X _ _ _ _ (level n c t hct (hb n).2).2⟩,
          (level n c t hct (hb n).2).1,
          c - 2 * d, t - 2 * d, (level n c t hct (hb n).2).2⟩,
      c - 2 * d, t - 2 * d, c - 2 * d, t - 2 * d,
      sub_le_sub_right hct _, sub_le_sub_right hct _, fun n ↦ ?_⟩
    exact ⟨tor_cohomology X _ _ _ _ (level n c t hct (hb n).2).2,
      (level n c t hct (hb n).2).2⟩
  · intro a z haz ht n
    exact ⟨tor_cohomology X _ _ _ _ (level n a z haz (ht n)).2,
      (level n a z haz (ht n)).2⟩

/-- Actual reductions, the finite purity square, and exceptional conjugacy for every
strict uniform constructible finite-Tor tower, including nonnormalized towers.
The finite isomorphisms are pinned by inverse diagonal orientation and the ordinary
tensor/counit transpose, rather than chosen to make the square commute.
Source: gamma proof (3) (blueprint: lem-sp-purity-conjugates-tower-reduction).
Proof: (1) pullbackTower_bounds establishes the domain. (2) Take the coefficient-adjoint
of the pulled-back transition, tensor the root transition, and use the canonical
pullback/tensor/scalar comparisons. On representatives both adjoints send x tensor b
to b times the pulled-back transition, with the root basis reduced to the target line.
This proves the pullback reduction equation below. (3) Tower gluing gives the actual
exceptional reduction as its counit mate followed by exceptional image of the actual
input reduction. (4) Apply det-sp-reduction-compatibilities to the finite quotient
rings, using scalar extension's constructible finite-Tor preservation even for a
nonflat quotient. (5) Apply naturality of det-sp-finite-general-ring to the actual
input reduction, not assumed invertible, and paste the two squares. The comparison
with the specified inverse-diagonal/tensor-transpose map is
lem-sp-finite-orientation-reduction. The displayed source and target comparisons
are the normalized site/realization transports of those maps. (6) Finite smooth
purity makes gamma invertible; scalar extension preserves its inverse. Cancel it
in the square to obtain conjugacy. No input reduction is inverted. -/
theorem purity_conjugates_tower_reduction
    (D : FiniteFieldDatum.{u}) [CharP D.k D.p] (hne : l ≠ D.p)
    {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [(j ≫ p).IsOver (Spec (.of D.k))]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]
    (w : SpChartAdmissibility.Twists l E X)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF G adj)
    (roots : SpCoordinateAdjunction.RootLines l E X)
    (unitsX : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤)))
    (cc : ∀ n : ℕ, SpTowerP1.CoefficientCoordinates l E n X (unitsX n))
    (tc : ∀ n : ℕ, SpTowerP1.TensorCoordinates l E n b X)
    (gc : ∀ n : ℕ, SpTowerP1.GeometricCoordinates l E n (j ≫ p))
    (K : SpTowerCalculus.C l E b q Y) :
    ∃ gamma : ∀ n : ℕ, ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj
          (pullbackTower l E o q (j ≫ p) w d K)) ≅
        ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj (G.obj K).obj),
      (∀ n : ℕ,
        IsIso (sourceComparison l E o q (SpTowerGamma.factorization j p) w d
          hF G adj lv roots unitsX cc tc gc n K) ∧
        IsIso (targetComparison l E o q (SpTowerGamma.factorization j p) hF G adj lv n K) ∧
        ∃ dg : Etale.FiniteRingSectionDeformation.Geometry d
            (pullback.fst (j ≫ p) (j ≫ p)) (pullback.diagonal (j ≫ p)),
        ∃ alpha : Etale.dualizingComplex (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n)) (j ≫ p) ≅
            (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n) (l ^ (n + 1))
          (SpTowerP1.levelAnnihilates l E n) X d),
          Etale.FiniteSmoothPurity.OrientationNormalized (SpTowerP1.levelRing l E n) (l ^ (n + 1))
            (pow_pos (Fact.out : l.Prime).pos _) (SpTowerP1.levelAnnihilates l E n)
            (j ≫ p) d dg (unitsX n) alpha ∧
          (sourceComparison l E o q (SpTowerGamma.factorization j p) w d
          hF G adj lv roots unitsX cc tc gc n K) ≫ (gamma n).hom =
            (reductionSite (SpTowerShriek.R l E n) X).map
              (Etale.FiniteSmoothPurity.gamma (SpTowerP1.levelRing l E n) (j ≫ p)
                (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n) (l ^ (n + 1))
          (SpTowerP1.levelAnnihilates l E n) X d) alpha
                ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K)) ≫
              (SpTowerGamma.finiteRightComparison (SpTowerShriek.R l E n) j p
                (lv.finite_closed n) (lv.right n) (lv.adjunction n)
                (lv.realization n)).inv.app _) ≫
            (targetComparison l E o q (SpTowerGamma.factorization j p) hF G adj lv n K)) ∧
      ∀ (m n : ℕ) (h : m ≤ n),
        ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).map
            ((lv.comparison n).hom.app K).hom ≫
          (SpTowerGluing.coefficientMate l E b (SpTowerGamma.factorization j p) m n h
            (lv.finite_closed n) (lv.finite_closed m) (lv.scalarX m n h) (lv.scalarY m n h)
            (lv.right n) (lv.right m) (lv.adjunction n) (lv.adjunction m)
            ((SpTowerGluing.level l E b q Y n).obj K)
            (lv.direct_image_iso m n h ((SpTowerGluing.level l E b q Y n).obj K))).hom ≫
          ((lv.right m).map (ObjectProperty.homMk
            (SpTowerCalculus.reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj))).hom =
          SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h) (G.obj K).obj ≫
            ((lv.comparison m).hom.app K).hom) ∧
        ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).map (gamma n).hom ≫
            SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h) (G.obj K).obj =
          (SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h)
          (pullbackTower l E o q (j ≫ p) w d K)) ≫ (gamma m).hom) ∧
        (SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h) (G.obj K).obj =
          (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).map (gamma n).inv ≫
            (SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h)
          (pullbackTower l E o q (j ≫ p) w d K)) ≫ (gamma m).hom) ∧
        ∃ e : Etale.FiniteSmoothPurity.CoefficientLineComparison
            (RingHom.ulift.{u + 1, u + 1, u, u} (SpTowerCalculus.quotient l E h))
            (l ^ (n + 1)) (l ^ (m + 1))
            (SpTowerP1.levelAnnihilates l E n) (SpTowerP1.levelAnnihilates l E m) X,
        ∃ r : (Etale.FiniteSmoothPurity.ordinaryScalar
            (RingHom.ulift.{u + 1, u + 1, u, u} (SpTowerCalculus.quotient l E h)) Y).obj
            ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K)) ⟶
            ((lv.realization m).origin.obj ((SpTowerGluing.level l E b q Y m).obj K)),
          ((reductionSiteScalarIso (SpTowerCalculus.quotient l E h) Y).inv.app
              ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K)) ≫
            (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) Y).map
              ((lv.realization n).originIso.hom.app _) ≫
            (SpTowerCalculus.reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj) =
          (reductionSite (SpTowerShriek.R l E m) Y).map r ≫
            (lv.realization m).originIso.hom.app _) ∧
          ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).map
              (sourceComparison l E o q (SpTowerGamma.factorization j p) w d
          hF G adj lv roots unitsX cc tc gc n K) ≫
              (SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h)
          (pullbackTower l E o q (j ≫ p) w d K)) =
            (reductionSiteScalarIso (SpTowerCalculus.quotient l E h) X).hom.app
              ((Etale.FiniteSmoothPurity.puritySource (SpTowerP1.levelRing l E n) (j ≫ p)
          (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n) (l ^ (n + 1))
          (SpTowerP1.levelAnnihilates l E n) X d)).obj
                ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K))) ≫
            (reductionSite (SpTowerShriek.R l E m) X).map
              ((Etale.FiniteSmoothPurity.pullbackTwistComparison (j ≫ p) d e
                ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K))).hom ≫
                (Etale.FiniteSmoothPurity.puritySource (SpTowerP1.levelRing l E m) (j ≫ p)
          (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E m) (l ^ (m + 1))
          (SpTowerP1.levelAnnihilates l E m) X d)).map r) ≫
              (sourceComparison l E o q (SpTowerGamma.factorization j p) w d
          hF G adj lv roots unitsX cc tc gc m K)) := by
  classical
  have : Smooth (j ≫ p) := SmoothOfRelativeDimension.smooth d (j ≫ p)
  have : LocallyOfFiniteType (j ≫ p) := inferInstance
  have orientations (n : ℕ) := finiteGeneralRingOrientation D l hne (j ≫ p) d
    (n + 1) (Nat.succ_pos n) (SpTowerShriek.R l E n)
    (SpTowerClasses.coefficient_annihilates l E n)
  choose eqv twist alpha dg hu hi he hn using orientations
  let A := alpha
  have halpha (n : ℕ) : Etale.FiniteSmoothPurity.OrientationNormalized
      (SpTowerP1.levelRing l E n) (l ^ (n + 1))
      (pow_pos (Fact.out : l.Prime).pos _) (SpTowerP1.levelAnnihilates l E n)
      (j ≫ p) d (dg n) (unitsX n) (A n) := hn n
  let beta (n : ℕ) :=
    (reductionSite (SpTowerShriek.R l E n) X).map
      (Etale.FiniteSmoothPurity.gamma (SpTowerP1.levelRing l E n) (j ≫ p)
        (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n) (l ^ (n + 1))
          (SpTowerP1.levelAnnihilates l E n) X d) (A n)
        ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K)) ≫
        (SpTowerGamma.finiteRightComparison (SpTowerShriek.R l E n) j p
          (lv.finite_closed n) (lv.right n) (lv.adjunction n)
          (lv.realization n)).inv.app _) ≫
      (targetComparison l E o q (SpTowerGamma.factorization j p) hF G adj lv n K)
  have hs (n : ℕ) := sourceComparison_isIso l E o q (SpTowerGamma.factorization j p)
    w d hF G adj lv roots unitsX cc tc gc n K
  have ht (n : ℕ) : IsIso
      (targetComparison l E o q (SpTowerGamma.factorization j p) hF G adj lv n K) := by
    dsimp only [targetComparison, SpTowerGamma.targetWord]
    infer_instance
  have hb (n : ℕ) : IsIso (beta n) := by
    have hY : ∀ y : Y, IsUnit ((l ^ (n + 1) : ℕ) : Y.presheaf.stalk y) := by
      intro y
      simpa only [map_natCast, finiteGeneralRingPrimeSetting,
        PurityFiniteSetting.diagonalExponent] using
        ((finiteGeneralRingPrimeSetting D l hne (n + 1) (Nat.succ_pos n)).diagonalExponent_isUnit
          (Y ↘ Spec (.of D.k))).map (Y.presheaf.germ ⊤ y trivial).hom
    have := (Etale.smooth_tensor_duality (SpTowerP1.levelRing l E n) (l ^ (n + 1))
      (pow_pos (Fact.out : l.Prime).pos _) (SpTowerP1.levelAnnihilates l E n) hY
      (j ≫ p) d).2
      ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K))
    have : IsIso (Etale.FiniteSmoothPurity.gamma (SpTowerP1.levelRing l E n) (j ≫ p)
        (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n) (l ^ (n + 1))
          (SpTowerP1.levelAnnihilates l E n) X d) (A n)
        ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K))) := by
      unfold Etale.FiniteSmoothPurity.gamma
      infer_instance
    dsimp only [beta]
    infer_instance
  let gamma (n : ℕ) :=
    (asIso (sourceComparison l E o q (SpTowerGamma.factorization j p) w d
      hF G adj lv roots unitsX cc tc gc n K)).symm ≪≫ asIso (beta n)
  have hgamma (n : ℕ) :
      sourceComparison l E o q (SpTowerGamma.factorization j p) w d
        hF G adj lv roots unitsX cc tc gc n K ≫ (gamma n).hom = beta n := by
    simp only [gamma, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, IsIso.hom_inv_id_assoc]
  refine ⟨gamma, ?_, ?_⟩
  · intro n
    exact ⟨hs n, ht n, dg n, A n, halpha n, hgamma n⟩
  · intro m n h
    obtain ⟨e, r, hr, hp⟩ := pullback_reduction_transport l E o q D hne j p d w
      hF G adj lv roots unitsX cc tc gc K m n h
    have hf := finite_purity_reduction_transport l E o q D hne j p d
      hF G adj lv unitsX K dg A m n h (halpha n) (halpha m) e r hr
    have square :
        (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).map (gamma n).hom ≫
          SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h) (G.obj K).obj =
        SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h)
          (pullbackTower l E o q (j ≫ p) w d K) ≫ (gamma m).hom := by
      apply (cancel_epi ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).map
        (sourceComparison l E o q (SpTowerGamma.factorization j p) w d
          hF G adj lv roots unitsX cc tc gc n K))).mp
      rw [← Category.assoc, ← Functor.map_comp, hgamma]
      rw [← Category.assoc, hp]
      simp only [Category.assoc, hgamma]
      simpa only [Category.assoc] using hf
    refine ⟨lv.reduction m n h K, square, ?_, e, r, hr, hp⟩
    calc
      _ = (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).map
          (gamma n).inv ≫
          ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).map
            (gamma n).hom ≫
            SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h)
              (G.obj K).obj) := by
        simp only [← Category.assoc, Iso.map_inv_hom_id, Category.id_comp]
      _ = _ := by rw [square]

end AlgebraicGeometry.ProEtale.SpPurityReduction

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
