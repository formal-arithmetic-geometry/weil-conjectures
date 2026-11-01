/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.CondensedTateIntegralTowerData
import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.TateTensorDerivedOrdinaryNormalization
import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.TateTensorRealizedSingleModel

/-! The finite Tate transition on ordinary root generators.

Source: smooth-purity transport, normalized Tate tower, Step 4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

private theorem finiteModelIso_eq_realizedShiftModel
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n d : ℕ)
    (hu : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(T, ⊤))) :
    finiteModelIso T ell hT n d =
      realizedShiftModel T ell n (2 * (d : ℤ))
        (Etale.CoordinateCounitArrows.baseTateIso (coefficient ell (n + 1))
          (ell ^ (n + 1)) (pow_pos (Fact.out : ell.Prime).pos _)
          (CharP.cast_eq_zero _ _) T hu d) := by
  apply Iso.ext
  rfl

attribute [local irreducible] finiteModelIso in
private theorem finiteTateTensor_transition_model_core
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d b a : ℕ) (hab : a ≤ b)
    (r : CoefficientLineComparison
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
      (ell ^ (b + 1)) (ell ^ (a + 1))
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T) :
    (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) b)).map
          ((pbcDerivedScalarAdjunction (pbcAdicQuotient T (datum.{u} ell) b a hab)).homEquiv
            _ _ ((scalarComparison T ell b a hab).hom.app (finiteTwist T ell b d) ≫
              (derivedRealization T ell a).map (proTwistMap d r))) ≫
        (pbcDerivedRestrictComp (pbcAdicProjection T (datum.{u} ell) b)
          (pbcAdicQuotient T (datum.{u} ell) b a hab)
          (pbcAdicProjection T (datum.{u} ell) a)
          (pbcAdicProjection_comp T (datum.{u} ell) b a hab)).hom.app _ ≫
        (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) a)).map
          (finiteModelIso T ell hT a d).hom ≫
        (Functor.mapDerivedCategorySingleFunctor
          (pbcRestrict (pbcAdicProjection T (datum.{u} ell) a)) (-(2 * (d : ℤ)))).hom.app _ =
      (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) b)).map
          (finiteModelIso T ell hT b d).hom ≫
        (Functor.mapDerivedCategorySingleFunctor
          (pbcRestrict (pbcAdicProjection T (datum.{u} ell) b)) (-(2 * (d : ℤ)))).hom.app _ ≫
        (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).map
          (finiteTateOrdinaryTransition T ell d b a hab r) := by
  have hb : IsUnit ((ell ^ (b + 1) : ℕ) : Γ(T, ⊤)) := by
    simpa only [Nat.cast_pow] using hT.pow (b + 1)
  have ha : IsUnit ((ell ^ (a + 1) : ℕ) : Γ(T, ⊤)) := by
    simpa only [Nat.cast_pow] using hT.pow (a + 1)
  have ht := finiteTateEtaleTransition_derived r
    (pow_pos (Fact.out : ell.Prime).pos _) (pow_pos (Fact.out : ell.Prime).pos _) hb ha d
  have h := realizedSemilinear_derived T ell b a hab (2 * (d : ℤ))
    (Etale.CoordinateCounitArrows.baseTateIso (coefficient ell (b + 1))
      (ell ^ (b + 1)) (pow_pos (Fact.out : ell.Prime).pos _) (CharP.cast_eq_zero _ _)
      T hb d)
    (Etale.CoordinateCounitArrows.baseTateIso (coefficient ell (a + 1))
      (ell ^ (a + 1)) (pow_pos (Fact.out : ell.Prime).pos _) (CharP.cast_eq_zero _ _)
      T ha d)
    (r.tensorPower d).hom (finiteTateEtaleTransition r d) ht
  rw [finiteModelIso_eq_realizedShiftModel T ell hT a d ha,
    finiteModelIso_eq_realizedShiftModel T ell hT b d]
  exact h

end AlgebraicGeometry.Scheme.PurityIntegralTower
