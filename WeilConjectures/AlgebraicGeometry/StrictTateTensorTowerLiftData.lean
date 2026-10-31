/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedTateIntegralTowerData
import WeilConjectures.AlgebraicGeometry.StrictTateTensorTowerLiftPre
import WeilConjectures.AlgebraicGeometry.StrictTateTensorTowerSingleCocycle

/-! Data for the strict ordinary Tate quotient tower.

Source: smooth-purity transport, normalized Tate tower, Steps 2--3.
(blueprint: lem-pur-strict-tate-tensor-tower-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

/-- The strict quotient tower has quotient-linear single-complex levels.

This is the construction part of the strict Tate tensor tower lift.  It records
only the tower, its quotient-level identifications, and the identification with
the strict derived tower; the evaluation equation is isolated in the companion
lemma `strictTateTensorTower_evaluation`.

Proof source: current blueprint, sec-smooth-purity/sk-thm-purity-transport,
Steps 2--3; K-flatness and quotient balancing for the actual integral root line.
The root line is locally the completed coefficient unit, so its tensor powers are
K-flat in the displayed single degree.  Ordinary quotient balancing therefore
constructs the normalized levels and the strict tower structure, including equal
indices and the zeroth tensor power.
(blueprint: lem-pur-strict-tate-tensor-tower-data)
-/
theorem strictTateTensorTower_data
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ) :
    ∃ (M : AdicTower T (datum.{u} ell))
      (q : ∀ n : ℕ, M.level n ≅
        (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj
          (quotientLine T ell n d)),
      M.tower = strictDerivedTower T ell d := by
  obtain ⟨P, q, h⟩ := strictTateTensorTower_pre T ell hT d
  let M := P.toAdicTower (strictTateTensorTower_single_pre_cocycle T (datum.{u} ell) P
    (-(2 * (d : ℤ))) (fun n ↦ quotientLine T ell n d) q)
  refine ⟨M, (fun n => q n), ?_⟩
  exact h

end AlgebraicGeometry.Scheme.PurityIntegralTower
