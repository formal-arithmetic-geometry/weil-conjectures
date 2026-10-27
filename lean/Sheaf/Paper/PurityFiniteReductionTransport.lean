/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.Paper.PurityTowerReductionComparisons

/-! # Finite purity reduction transport

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

/-- Coefficient compatibility and naturality of the finite purity arrows in the
specified exceptional-output coordinates, before any tower purity arrow is assembled.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md, (3),
coefficient compatibility followed by naturality at the actual input reduction.
(blueprint: lem-sp-purity-finite-reduction-transport).

Proof: finite_orientation_reduction identifies scalar extension of the normalized
inverse diagonal orientation with the target orientation followed by the root-line
comparison. Geometry is a proposition, so the two geometric witnesses agree.
Tensor compatibility of the counit-characterized exceptional coefficient mate and
this orientation equation give the ordinary finite purity coefficient square, also
obtained from reductionCompatibilities_purity after common-exponent identification.
Apply ordinary purity naturality at r and paste. Transport this equality through
reductionSiteScalarIso. Uniqueness of right adjoints identifies finiteRightComparison
with the counit-normalized realization of the exceptional coefficient mate. Its counit
equation, the input equation hr and Levels.reduction identify the resulting output
composite with the actual exceptional tower reduction. Cancel the realization and
origin isomorphisms. The result is the displayed square for the finite arrows, with
no tower gamma supplied or chosen. Equal levels, rank zero, zero transitions and
nonflat quotients are included: the proof uses functoriality and transposition, never
invertibility of r. -/
theorem finite_purity_reduction_transport
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
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF G adj)
    (unitsX : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤)))
    (K : SpTowerCalculus.C l E b q Y)
    (dg : ∀ i : ℕ, Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst (j ≫ p) (j ≫ p)) (pullback.diagonal (j ≫ p)))
    (alpha : ∀ i : ℕ,
      Etale.dualizingComplex (ModuleCat.{u + 1} (SpTowerP1.levelRing l E i)) (j ≫ p) ≅
        (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E i) (l ^ (i + 1))
          (SpTowerP1.levelAnnihilates l E i) X d))
    (m n : ℕ) (h : m ≤ n)
    (hn : Etale.FiniteSmoothPurity.OrientationNormalized (SpTowerP1.levelRing l E n)
      (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _)
      (SpTowerP1.levelAnnihilates l E n) (j ≫ p) d (dg n) (unitsX n) (alpha n))
    (hm : Etale.FiniteSmoothPurity.OrientationNormalized (SpTowerP1.levelRing l E m)
      (l ^ (m + 1)) (pow_pos (Fact.out : l.Prime).pos _)
      (SpTowerP1.levelAnnihilates l E m) (j ≫ p) d (dg m) (unitsX m) (alpha m))
    (e : Etale.FiniteSmoothPurity.CoefficientLineComparison
            (RingHom.ulift.{u + 1, u + 1, u, u} (SpTowerCalculus.quotient l E h))
            (l ^ (n + 1)) (l ^ (m + 1))
            (SpTowerP1.levelAnnihilates l E n) (SpTowerP1.levelAnnihilates l E m) X)
    (r : (Etale.FiniteSmoothPurity.ordinaryScalar
            (RingHom.ulift.{u + 1, u + 1, u, u} (SpTowerCalculus.quotient l E h)) Y).obj
            ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K)) ⟶
            ((lv.realization m).origin.obj ((SpTowerGluing.level l E b q Y m).obj K)))
    (hr : (reductionSiteScalarIso (SpTowerCalculus.quotient l E h) Y).inv.app
              ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K)) ≫
            (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) Y).map
              ((lv.realization n).originIso.hom.app _) ≫
            (SpTowerCalculus.reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj) =
          (reductionSite (SpTowerShriek.R l E m) Y).map r ≫
            (lv.realization m).originIso.hom.app _) :
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).map
      ((reductionSite (SpTowerShriek.R l E n) X).map
      (Etale.FiniteSmoothPurity.gamma (SpTowerP1.levelRing l E n) (j ≫ p)
        (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n) (l ^ (n + 1))
          (SpTowerP1.levelAnnihilates l E n) X d) (alpha n)
          ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K)) ≫
        (SpTowerGamma.finiteRightComparison (SpTowerShriek.R l E n) j p
          (lv.finite_closed n) (lv.right n) (lv.adjunction n)
          (lv.realization n)).inv.app _) ≫
      (targetComparison l E o q (SpTowerGamma.factorization j p) hF G adj lv n K)) ≫
      SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h) (G.obj K).obj =
    ((reductionSiteScalarIso (SpTowerCalculus.quotient l E h) X).hom.app
      ((Etale.FiniteSmoothPurity.puritySource (SpTowerP1.levelRing l E n) (j ≫ p)
        (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n) (l ^ (n + 1))
          (SpTowerP1.levelAnnihilates l E n) X d)).obj
          ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K))) ≫
    (reductionSite (SpTowerShriek.R l E m) X).map
      ((Etale.FiniteSmoothPurity.pullbackTwistComparison (j ≫ p) d e
        ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K))).hom ≫
        (Etale.FiniteSmoothPurity.puritySource (SpTowerP1.levelRing l E m) (j ≫ p)
          (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E m) (l ^ (m + 1))
          (SpTowerP1.levelAnnihilates l E m) X d)).map r)) ≫
      ((reductionSite (SpTowerShriek.R l E m) X).map
      (Etale.FiniteSmoothPurity.gamma (SpTowerP1.levelRing l E m) (j ≫ p)
        (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E m) (l ^ (m + 1))
          (SpTowerP1.levelAnnihilates l E m) X d) (alpha m)
          ((lv.realization m).origin.obj ((SpTowerGluing.level l E b q Y m).obj K)) ≫
        (SpTowerGamma.finiteRightComparison (SpTowerShriek.R l E m) j p
          (lv.finite_closed m) (lv.right m) (lv.adjunction m)
          (lv.realization m)).inv.app _) ≫
      (targetComparison l E o q (SpTowerGamma.factorization j p) hF G adj lv m K)) := by sorry

end AlgebraicGeometry.ProEtale.SpPurityReduction

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
