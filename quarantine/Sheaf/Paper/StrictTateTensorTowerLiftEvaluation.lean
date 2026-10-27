/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CondensedTateIntegralTowerData

/-! Evaluation identity for strict ordinary Tate quotient towers.

Source: smooth-purity transport, normalized Tate tower, Steps 2--3.
(blueprint: lem-pur-strict-tate-tensor-tower-evaluation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

/-- A strict quotient tower with the prescribed single-complex levels has the
exact restriction/evaluation comparison displayed in the lift theorem.

Proof source: current blueprint, sec-smooth-purity/sk-thm-purity-transport,
Steps 2--3.  Exact restriction and evaluation of a single complex identify the
left hand side with the ordinary quotient projection.  The strict tower equality
then rewrites the final evaluation map, yielding the displayed equation.
(blueprint: lem-pur-strict-tate-tensor-tower-evaluation)
-/
theorem strictTateTensorTower_evaluation
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ)
    (M : AdicTower T (datum.{u} ell))
    (q : ∀ n : ℕ, M.level n ≅
      (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj
        (quotientLine T ell n d))
    (h : M.tower = strictDerivedTower T ell d) :
    ∀ n : ℕ,
      (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) n)).map (q n).inv ≫
          (M.evaluation n).hom ≫
          (pbcTowerEvaluation T (pbcAdicCompletion T (datum.{u} ell)) n).map
            (eqToHom h) =
        (Functor.mapDerivedCategorySingleFunctor
          (pbcRestrict (pbcAdicProjection T (datum.{u} ell) n))
          (-(2 * (d : ℤ)))).hom.app (quotientLine T ell n d) ≫
        (Functor.mapDerivedCategorySingleFunctor
          ((CategoryTheory.evaluation ℕᵒᵖ
            (pbcModules T (pbcAdicCompletion T (datum.{u} ell)))).obj (op n))
          (-(2 * (d : ℤ)))).inv.app (strictTower T ell d) := by
  sorry

end AlgebraicGeometry.Scheme.PurityIntegralTower
