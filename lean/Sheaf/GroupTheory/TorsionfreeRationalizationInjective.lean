/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.GroupTheory.RationalRank
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Torsion-free groups inject into their rationalization

Source: Temkin, *Stable modification of relative curves*, §2.1, pp. 7–8
(blueprint: lem-trf-torsionfree-rationalization-injective).
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace AddCommGroup

/-- The canonical map from an abelian group to its rationalization sends `g` to `1 ⊗ g`.
Source: Temkin, §2.1, pp. 7–8 (blueprint: lem-trf-torsionfree-rationalization-injective). -/
noncomputable def rationalizationMap (G : Type u) [AddCommGroup G] :
    G →+ (ℚ ⊗[ℤ] G) :=
  AddMonoidHom.mk' (fun g => TensorProduct.mk ℤ ℚ G 1 g)
    (fun _ _ => TensorProduct.tmul_add _ _ _)

/-- A torsion-free abelian group injects into its rationalization.
Source: Temkin, *Stable modification of relative curves*, §2.1, pp. 7–8
(blueprint: lem-trf-torsionfree-rationalization-injective).

Proof plan:
1. Localize `ℤ` at its nonzero elements. Sending an integer fraction to its rational
   value identifies this ring with `ℚ`, since both equality relations are cross multiplication.
2. The tensor-product universal property (`def-weil-pbc-module-tensor-product`) gives inverse
   maps `ℤ ⊗[ℤ] G → G`, `a ⊗ g ↦ a • g`, and `g ↦ 1 ⊗ g`. Localize these maps using
   `def-weil-pbc-module-localization`; their composites remain identities on fractions.
3. The comparison `lem-weil-pbc-localization-tensor-over-base` identifies the localization
   of `ℤ ⊗[ℤ] G` with the tensor product of the localized integers and `G`. Together with
   steps 1 and 2 this identifies the localized group with `ℚ ⊗[ℤ] G`, sending `g/s` to
   `(1/s) ⊗ g`. Tensor symmetry identifies this with the source's `G ⊗[ℤ] ℚ`.
4. If two canonical images agree, the localization kernel criterion gives a nonzero
   integer `s` annihilating their difference. Apply the hypothesis to `s` when positive
   and to `-s` otherwise. Their difference is zero, proving injectivity. -/
theorem rationalizationMap_injective (G : Type u) [AddCommGroup G]
    (hT : ∀ (m : ℤ) (g : G), 0 < m → m • g = 0 → g = 0) :
    Function.Injective (rationalizationMap G) := by
  sorry

end AddCommGroup
