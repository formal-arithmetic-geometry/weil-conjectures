/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.CompactFlatBarUnion
import Sheaf.AlgebraicGeometry.CompactFlatBarHomotopyComparison

/-! # The canonical union augmentation in the homotopy category

This combines the target-chain comparison with the proved strict section and the
proved canonical identification of the sequential cokernel with the full bar.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
namespace CompactFlatBarIndex

variable {Y : Scheme.{u}}
  {L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
  {l : ∀ n : ℕ, L n ⟶ L (n + 1)}
  (D : CompactFlatFiniteSubcomplexDiagrams Y L l)
  (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
  (t : ∀ n : ℕ, E n ⟶ E (n + 1))
  (p : ∀ n : ℕ, L n ⟶ CochainComplex.mappingCone (flatTelescopeDifferential E t))
  (hp : ∀ n : ℕ, l n ≫ p (n + 1) = p n)

/-- Full-bar augmentation in the homotopy category.

Source: the corresponding paragraph of
`lem-sc-compact-flat-bar-union-augmentation`, expanded by SHEAF group P2.
(blueprint: lem-sc-compact-flat-bar-union-homotopy).

Proof: Apply the unit contraction and target-chain comparison. The strict section, augmentation
identity, and cancellation lemma then make the full-bar augmentation invertible. -/
lemma fullBarAugmentation_isIso :
    IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (fullBarAugmentation D E t p hp)) := by
  obtain ⟨⟨h⟩, ht⟩ := targetComparison D E t p hp
  exact fullBarAugmentation_isIso_of_target D E t p hp h ht

/-- Canonical cokernel augmentation in the homotopy category.

Source: the corresponding paragraph of
`lem-sc-compact-flat-bar-union-augmentation`, expanded by SHEAF group P2.
(blueprint: lem-sc-compact-flat-bar-cokernel-homotopy).

Proof: Under unionIso the cokernel.desc map is the composite of the canonical cokernel-to-full-bar
isomorphism and the full-bar augmentation. The quotient functor preserves the first
isomorphism; the second is invertible by fullBarAugmentation_isIso. Their composite is
invertible. -/
lemma cokernelAugmentation_isIso
    (hz : flatTelescopeDifferential (enlargedBar D E t p hp)
      (enlargedBarMap D E t p hp) ≫
        Sigma.desc (enlargedBarAugmentation D E t p hp) = 0) :
    IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (cokernel.desc (flatTelescopeDifferential (enlargedBar D E t p hp)
        (enlargedBarMap D E t p hp))
          (Sigma.desc (enlargedBarAugmentation D E t p hp)) hz)) := by
  rw [← unionIso_augmentation D E t p hp hz, Functor.map_comp]
  have := fullBarAugmentation_isIso D E t p hp
  infer_instance

end CompactFlatBarIndex
end AlgebraicGeometry
