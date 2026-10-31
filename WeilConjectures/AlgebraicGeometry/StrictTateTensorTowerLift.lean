/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedTateIntegralTowerData
import WeilConjectures.AlgebraicGeometry.StrictTateTensorTowerLiftData
import WeilConjectures.AlgebraicGeometry.StrictTateTensorTowerLiftEvaluation

/-! Derived levels of the strict ordinary quotient tower.

Source: smooth-purity transport, normalized Tate tower, Steps 2--3.
(blueprint: lem-pur-strict-tate-tensor-tower-lift)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

/-- Lift the strict ordinary quotient tower to quotient-linear derived levels.
The level identifications land in single complexes of the actual ordinary quotients;
they involve neither finite etale twists nor root-line comparison maps.

Source: current blueprint, sec-smooth-purity/sk-thm-purity-transport, Step 2;
lem-pur-normalized-tate-tensor-reductions, proof Steps 2--3.
(blueprint: lem-pur-strict-tate-tensor-tower-lift)

Proof: the actual integral root line is locally the completed coefficient unit on
a common primitive-root covering. Tensor powers, including the zeroth power, remain
free rank one there. A single complex of such a line is K-flat: tensor with an
acyclic complex becomes that complex with a degree shift on this covering; exact
restriction and local detection of vanishing cohomology prove acyclicity globally.
Derived scalar extension is therefore computed by the ordinary quotient sheaf.
Take the tower to be strictDerivedTower, the levels to be the single complexes of
quotientLine, and evaluation to be the exact single/evaluation comparison. For every
b >= a, normalization is derived quotient balancing, represented on pure tensors by
((x tensor c) tensor a) mapping to x tensor q(c)a. Its inverse inserts a unit.
The normalized scalar adjunction identifies its semilinear adjunct with the strict
quotient transition. For c >= b >= a, both composites multiply the same residue
scalars, proving the cocycle; this also applies at equal indices. These data define
AdicTower. Take q to be the identity on the chosen single-complex levels and h to be
reflexivity. The displayed equation is then the definition of evaluation, with the
exact restriction/single and evaluation/single comparisons on its two sides. -/
theorem strictTateTensorTower_lift
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ) :
    ∃ (M : AdicTower T (datum.{u} ell))
      (q : ∀ n : ℕ, M.level n ≅
        (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj
          (quotientLine T ell n d))
      (h : M.tower = strictDerivedTower T ell d),
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
  obtain ⟨M, q, h⟩ := strictTateTensorTower_data T ell hT d
  obtain ⟨q', hq'⟩ := strictTateTensorTower_evaluation T ell hT d M q h
  exact ⟨M, q', h, hq'⟩

end AlgebraicGeometry.Scheme.PurityIntegralTower
