/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Closed immersions under composition and fibre products

Source: Weil conjectures blueprint, `sec-curve-estimates/sk-thm-br`,
(blueprint: lem-weil-pbc-closed-immersion-products); Stacks Project, Tags 01QS, 01QR,
01T0 and 01T2.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Closed immersions compose and their products over a common base are closed immersions;
quasi-compact open immersions are of finite type.
Source: Weil conjectures blueprint, `sec-curve-estimates/sk-thm-br`, and Stacks Project,
Tags 01QS, 01QR, 01T0 and 01T2 (blueprint: lem-weil-pbc-closed-immersion-products).

Proof:
1. Composition is the Mathlib leaf `lem-weil-pbc-closed-immersion-comp` (Tag 01QS).
2. Factor the product through `W₁ ×_S Z₂`. Each factor is a base change of one given
   closed immersion, so `lem-weil-pbc-closed-immersion-base-change` applies (Tag 01QR).
3. Compose these factors using `lem-weil-pbc-closed-immersion-comp`.
4. An open immersion is locally of finite type. Together with quasi-compactness this
   gives finite type, by `lem-weil-pbc-qc-open-immersion-finite-type` (Tags 01T0 and 01T2). -/
theorem closedImmersion_comp_products_and_finiteType_openImmersion :
    (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      IsClosedImmersion f → IsClosedImmersion g → IsClosedImmersion (f ≫ g)) ∧
    (∀ {Z₁ Z₂ W₁ W₂ S : Scheme.{u}}
      (a₁ : Z₁ ⟶ S) (a₂ : Z₂ ⟶ S) (b₁ : W₁ ⟶ S) (b₂ : W₂ ⟶ S)
      (i₁ : Z₁ ⟶ W₁) (i₂ : Z₂ ⟶ W₂)
      (h₁ : a₁ ≫ 𝟙 S = i₁ ≫ b₁) (h₂ : a₂ ≫ 𝟙 S = i₂ ≫ b₂),
      IsClosedImmersion i₁ → IsClosedImmersion i₂ →
        IsClosedImmersion (pullback.map a₁ a₂ b₁ b₂ i₁ i₂ (𝟙 S) h₁ h₂)) ∧
    (∀ {U Y : Scheme.{u}} (j : U ⟶ Y),
      IsOpenImmersion j → QuasiCompact j → (LocallyOfFiniteType j ∧ QuasiCompact j)) := by
  sorry

end AlgebraicGeometry
