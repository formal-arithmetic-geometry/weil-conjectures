/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTowerReductionComparisons

/-! # Actual pullback reduction transport

Source: tower-geometric gamma proof (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
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

/-- The actual twisted-pullback reduction in the retained ordinary origins.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md, (3),
pullback and twist commute with extension of scalars.
(blueprint: lem-sp-purity-pullback-reduction-transport).

Proof: the root power map gives the generator-normalized coefficient line comparison.
The input origin comparison is invertible on the constructible finite-Tor domain.
Use the site/scalar comparison and its inverse origin comparison to transport the
actual input reduction, obtaining r and the first equation. The transition of the
strict pullback tensor tower is the pulled-back input transition tensored with the
root transition. Transpose it under coefficient extension/restriction. On K-flat
representatives both paths send x tensor b to b times the pulled-back transition of x,
and the root generator to its power-map image. The normalized scalar/pullback,
tensor and even-shift comparisons therefore give the second equation after deriving.
Insert the realization counit and evaluation comparisons; their naturality and
triangle identities give exactly sourceComparison. No input reduction is inverted.
At m=n the root power and scalar comparisons are the unit constraints. For d=0
only the scalar unit remains. Zero objects and empty schemes satisfy both equations;
the K-flat argument also applies to nonflat quotients. -/
theorem pullback_reduction_transport
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
    (K : SpTowerCalculus.C l E b q Y) (m n : ℕ) (h : m ≤ n) :
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
          hF G adj lv roots unitsX cc tc gc m K)) := by sorry

end AlgebraicGeometry.ProEtale.SpPurityReduction

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
