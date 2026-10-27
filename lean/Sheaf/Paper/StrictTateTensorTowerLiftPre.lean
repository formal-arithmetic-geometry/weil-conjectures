/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CondensedTateIntegralTowerData

/-! A pre-tower for the strict ordinary Tate quotient construction.

The cocycle equation is kept separate from the other fields so that the
construction and its coherence can be proved independently.
(blueprint: lem-pur-strict-tate-tensor-tower-data-pre)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

structure StrictTateTensorTowerPre (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) where
  tower : DerivedCategory (pbcTowers T (pbcAdicCompletion T d))
  level : ∀ n : ℕ, DerivedCategory (pbcModules T ((pbcAdicRings T d).obj (op n)))
  evaluation : ∀ n : ℕ,
    (pbcDerivedRestrict (pbcAdicProjection T d n)).obj (level n) ≅
      (pbcTowerEvaluation T (pbcAdicCompletion T d) n).obj tower
  normalization : ∀ (b a : ℕ) (hab : a ≤ b),
    (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).obj (level b) ≅ level a
  transition : ∀ (b a : ℕ) (hab : a ≤ b),
    (pbcDerivedRestrict (pbcAdicProjection T d b)).map
        (adicTowerSemilinearTransition T d level normalization b a hab) ≫
      (pbcDerivedRestrictComp (pbcAdicProjection T d b)
        (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
        (pbcAdicProjection_comp T d b a hab)).hom.app (level a) ≫
      (evaluation a).hom =
    (evaluation b).hom ≫
      (pbcTowerTransition T (pbcAdicCompletion T d) b a hab).app tower

def StrictTateTensorTowerPre.Cocycle
    {T : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    {d : AdicCoefficientDatum A} (P : StrictTateTensorTowerPre T d) : Prop :=
  ∀ (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c),
    adicTowerSemilinearTransition T d P.level P.normalization c a
        (hab.trans hbc) =
      adicTowerSemilinearTransition T d P.level P.normalization c b hbc ≫
        (pbcDerivedRestrict (pbcAdicQuotient T d c b hbc)).map
          (adicTowerSemilinearTransition T d P.level P.normalization b a hab) ≫
        (pbcDerivedRestrictComp (pbcAdicQuotient T d c b hbc)
          (pbcAdicQuotient T d b a hab)
          (pbcAdicQuotient T d c a (hab.trans hbc))
          (pbcAdicQuotient_comp T d c b a hab hbc)).hom.app (P.level a)

def StrictTateTensorTowerPre.toAdicTower
    {T : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    {d : AdicCoefficientDatum A}
    (P : StrictTateTensorTowerPre T d)
    (hc : P.Cocycle) :
    AdicTower T d :=
  { tower := P.tower
    level := P.level
    evaluation := P.evaluation
    normalization := P.normalization
    transition := P.transition
    cocycle := hc }

/-- The strict quotient construction supplies every pre-tower field and the
single-complex comparisons; only the cocycle calculation is omitted here.

Proof source: smooth-purity transport, normalized Tate tower, Steps 2--3.
The quotient-linear levels are obtained by ordinary tensor balancing on the
locally free root line, and exact single-complex evaluation identifies them
with the displayed quotient lines. The strict tower is used as the tower
component, with its projection evaluations and quotient normalizations.
(blueprint: lem-pur-strict-tate-tensor-tower-data-pre)
-/
theorem strictTateTensorTower_pre
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ) :
    ∃ (P : StrictTateTensorTowerPre T (datum.{u} ell))
      (q : ∀ n : ℕ, P.level n ≅
        (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj
          (quotientLine T ell n d)),
      P.tower = strictDerivedTower T ell d := by
  sorry

end AlgebraicGeometry.Scheme.PurityIntegralTower
