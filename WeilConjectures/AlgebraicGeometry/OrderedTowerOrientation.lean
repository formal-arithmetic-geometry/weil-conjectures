/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGammaData

/-! # Diagonal orientation in the ordered strict-tower presentation

Source: latest blueprint tower-geometric gamma proof (1).
(blueprint: lem-sp-ordered-tower-orientation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerGamma
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- The coefficient-unit and diagonal-orientation part of FiniteLevels.
Source: gamma proof (1) (blueprint: lem-sp-ordered-tower-orientation). -/
def OrderedDiagonalLevels {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)] (d : ℕ)
    (w : SpChartAdmissibility.Twists l E X)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q (factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q (factorization j p) hF G adj)
    (unit_mem : spConstructibleTorTowers l E Y (q.abelian Y) (originalUnit l E b q Y))
    (roots : SpCoordinateAdjunction.RootLines l E X)
    (unitsX : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤)))
    (coefficientsX : ∀ n : ℕ,
      letI : Finite (SpTowerShriek.R l E n) := b.finite n
      SpTowerP1.CoefficientCoordinates l E n X (unitsX n))
    (unitsY : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(Y, ⊤)))
    (coefficientsY : ∀ n : ℕ,
      letI : Finite (SpTowerShriek.R l E n) := b.finite n
      SpTowerP1.CoefficientCoordinates l E n Y (unitsY n))
    (tensors : ∀ n : ℕ,
      letI : Finite (SpTowerShriek.R l E n) := b.finite n
      SpTowerP1.TensorCoordinates l E n b X)
    (orientation : orderedLine l E b X w d ≅
      (exceptional l E b q G).obj ⟨originalUnit l E b q Y, unit_mem⟩)
 : Prop :=
  ∀ n : ℕ,
    letI : Finite (SpTowerShriek.R l E n) := b.finite n
    ∃ dg : Etale.FiniteRingSectionDeformation.Geometry d
        (pullback.fst (j ≫ p) (j ≫ p)) (pullback.diagonal (j ≫ p)),
    ∃ alpha : Etale.dualizingComplex (SpTowerP1.levelRing l E n) (j ≫ p) ≅
        (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n)
          (l ^ (n + 1)) (SpTowerP1.levelAnnihilates l E n) X d),
      Etale.FiniteSmoothPurity.OrientationNormalized (SpTowerP1.levelRing l E n) (l ^ (n + 1))
        (pow_pos (Fact.out : l.Prime).pos _) (SpTowerP1.levelAnnihilates l E n)
        (j ≫ p) d dg (unitsX n) alpha ∧
    ∃ ui : ((lv.realization n).origin.obj
        ((SpTowerGluing.level l E b q Y n).obj
          ⟨originalUnit l E b q Y, unit_mem⟩)) ≅
        Etale.ordinaryFiniteUnit (SpTowerP1.levelRing l E n) Y,
      (SpTowerP1.nu l E n Y).map ui.hom ≫
          (SpTowerP1.unitWord l E n Y (coefficientsY n)).comparison =
        (inputWord l E b o q (factorization j p) hF G adj lv n
          ⟨originalUnit l E b q Y, unit_mem⟩).comparison ≫
          (SpTowerShriek.Ev l E Y n).map
            ((SpTowerCalculus.realization l E b Y (q.abelian Y)).counitIso.hom.app
              (unit l E Y)) ∧
      SpTowerP1.WordComparison l E n
        (coefficientWord l E b X w roots n (unitsX n) (coefficientsX n) (tensors n) d)
        (targetWord l E b o q (factorization j p) hF G adj lv n
          ⟨originalUnit l E b q Y, unit_mem⟩) orientation.hom
        (alpha.inv ≫ (finiteRightComparison (SpTowerShriek.R l E n) j p
            (lv.finite_closed n) (lv.right n) (lv.adjunction n) (lv.realization n)).inv.app _ ≫
          (lv.realization n).right.map ui.inv)

/-- The ordered diagonal orientation and its exact finite evaluation data.
This stores clause (1) only; there is no purity or normalization field.
Source: gamma proof (1) (blueprint: lem-sp-ordered-tower-orientation). -/
structure OrderedOrientation {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)] (d : ℕ)
    (w : SpChartAdmissibility.Twists l E X)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q (factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q (factorization j p) hF G adj) where
  unit_mem : spConstructibleTorTowers l E Y (q.abelian Y) (originalUnit l E b q Y)
  tensorX : SpTowerP1.TensorData l E b X
  tensorY : SpTowerP1.TensorData l E b Y
  roots : SpCoordinateAdjunction.RootLines l E X
  unitsX : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))
  unitsY : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(Y, ⊤))
  coefficientsX : ∀ n : ℕ,
    letI : Finite (SpTowerShriek.R l E n) := b.finite n
    SpTowerP1.CoefficientCoordinates l E n X (unitsX n)
  coefficientsY : ∀ n : ℕ,
    letI : Finite (SpTowerShriek.R l E n) := b.finite n
    SpTowerP1.CoefficientCoordinates l E n Y (unitsY n)
  tensors : ∀ n : ℕ,
    letI : Finite (SpTowerShriek.R l E n) := b.finite n
    SpTowerP1.TensorCoordinates l E n b X
  geometry : ∀ n : ℕ,
    letI : Finite (SpTowerShriek.R l E n) := b.finite n
    SpTowerP1.GeometricCoordinates l E n (j ≫ p)
  orientation : orderedLine l E b X w d ≅
    (exceptional l E b q G).obj ⟨originalUnit l E b q Y, unit_mem⟩
  diagonal_levels : OrderedDiagonalLevels l E b o q j p d w hF G adj lv unit_mem
    roots unitsX coefficientsX unitsY coefficientsY tensors orientation

/-- The diagonal orientation and its section-normalized coefficient presentations.
This is only the orientation construction; no tensor transpose, purity isomorphy or
preservation of normalized towers is asserted.
Source: latest blueprint tower-geometric gamma proof (1)
(blueprint: lem-sp-ordered-tower-orientation).

Proof: identify the ell-power quotients with the uniformizer quotients using the
ramification equation in b. Take the normalized scalar-unit, root, K-flat tensor
and pullback comparisons, which fix their maps on sections and representatives.
The finite diagonal theorem supplies the inverse orientations at every positive
level. FiniteOrientationReduction identifies their quotient squares with the
actual reductions of the given right adjoint at the coefficient unit. Remove the
common shift 2d. Scalar extension of the locally free Tate line is its ordinary
quotient, so StrictLineHeartAssembly assembles the compatible degree-zero sheaf
maps, and their inverses, into a strict tower isomorphism. Shift back and use the
ordered tensor/shift reassociation to obtain orientation. Its prescribed evaluation
is exactly DiagonalLevels, including the coefficient-unit equation. The zero-fold
line uses the coefficient unit, so the construction also applies at d=0. -/
theorem ordered_tower_orientation (D : FiniteFieldDatum.{u}) [CharP D.k D.p] (hne : l ≠ D.p)
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
        ((SpTowerCalculus.F l E b o q (factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q (factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q (factorization j p) hF G adj) :
    Nonempty (OrderedOrientation l E b o q j p d w hF G adj lv) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerGamma

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
