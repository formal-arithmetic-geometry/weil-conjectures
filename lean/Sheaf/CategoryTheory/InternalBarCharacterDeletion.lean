/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.CategoryTheory.InternalBarCharacterData

import Sheaf.CategoryTheory.CondensedFreeLinearizationTensor

/-! # Equivariant character deletion

The degree-one part of the internal bar character calculation.
Source: agent-written internal bar calculation, steps 1--2
(blueprint: lem-sfb-internal-bar-character-deletion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open Profinite.CondensedAction Profinite.CondensedAction.InternalBar
open CategoryTheory.CondensedDerivedRestriction (Character)
namespace Profinite.CondensedAction.InternalBarCharacter
variable {A : CategoryTheory.CondensedBar.Ring.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The natural character-deletion formula extends uniquely to a cochain map to P[1].
Source: lem-sfb-internal-bar-character-lifts, proof steps 1--2, in the agent-written
internal-bar expansion of blueprint direct-images paragraph (3).
(blueprint: lem-sfb-internal-bar-character-deletion).

Proof: For each n, assign to a tuple its tail generator multiplied by
 a(g_0⁻¹g_1). Restriction compatibility follows from the character's naturality,
the free-adjunction unit's naturality, and the semilinearity of restriction maps.
The free-module adjunction extends this natural assignment uniquely to an internal
linear map. On simultaneous left translations the ratio is unchanged, so the
generator equivariance criterion gives equivariance. For n >= 2 the terms in
boundary L + L boundary deleting positions i >= 2 cancel in pairs. The remaining
coefficient is a(g_0⁻¹g_1) + a(g_1⁻¹g_2) - a(g_0⁻¹g_2), which is zero because
(g_0⁻¹g_1)(g_1⁻¹g_2) = g_0⁻¹g_2 and a is additive. At degrees zero and one the
unaugmented endpoints vanish. Thus the components define a cochain map into the
shift, whose differential is the negative of the original one. Equality on the
free generators fixes every negative-degree component. All other components have
zero source or target, proving uniqueness. This also covers the zero ring, the
trivial group, and the empty profinite parameter.
-/
theorem exists_deletion (D : Resolution A.toMon G) (a : Character A G) :
    ∃ L : complex D ⟶ (complex D)⟦(1 : ℤ)⟧, IsLift D a L := by sorry

private theorem degreeOne_ext (D : Resolution A.toMon G)
    (L K : complex D ⟶ (complex D)⟦(1 : ℤ)⟧)
    (h : ∀ n, component D L n = component D K n) : L = K := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i < 0
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -((n + 1 : ℕ) : ℤ) :=
      ⟨(-i - 1).toNat, by omega⟩
    have hh := h n
    dsimp only [component] at hh
    have hh1 := (cancel_epi (termIso D (n + 1)).inv).mp hh
    simp only [← Category.assoc] at hh1
    have hh2 := (cancel_mono (termIso D n).hom).mp hh1
    have hh3 := (cancel_mono
      ((complex D).shiftFunctorObjXIso 1 (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
        (by omega)).hom).mp hh2
    exact hh3
  · by_cases hi0 : i = 0
    · subst i
      rw [degreeOne_zero D L, degreeOne_zero D K]
    · have hz : IsZero ((complex D).X i) :=
        (chains D).isZero_extend_X ComplexShape.embeddingDownNat i (by
          intro n
          change -(n : ℤ) ≠ i
          omega)
      exact hz.eq_of_src _ _

/-- The free-generator prescription uniquely determines a deletion lift.
Source: the free-module equality test in character-lift step 1
(blueprint: lem-sfb-internal-bar-character-deletion). -/
theorem deletion_unique (D : Resolution A.toMon G) (a : Character A G)
    (L K : complex D ⟶ (complex D)⟦(1 : ℤ)⟧)
    (hL : IsLift D a L) (hK : IsLift D a K) : L = K := by
  obtain ⟨c⟩ := Profinite.CondensedFreeLinearization.exists_comparison A.toMon
  apply degreeOne_ext D L K
  intro n
  apply (cancel_epi (D.freeIso (n + 1)).inv).mp
  apply c.generator_ext
  intro S x
  let y : Fin (n + 2) → C(S, G) := fun i ↦
    ⟨fun s ↦ x.down.hom.hom s i, (continuous_apply i).comp x.down.hom.hom.continuous⟩
  have hx : ULift.up (CompHausLike.ofHom _
      ⟨fun s i ↦ y i s, continuous_pi fun i ↦ (y i).continuous⟩) = x := by
    apply ULift.ext
    ext s i
    rfl
  have hh := (hL.2 n S y).trans (hK.2 n S y).symm
  change onSections A.toMon (component D L n) S
      (onSections A.toMon (D.freeIso (n + 1)).inv S
        (Profinite.CondensedFreeLinearization.generator A.toMon _ S x)) =
    onSections A.toMon (component D K n) S
      (onSections A.toMon (D.freeIso (n + 1)).inv S
        (Profinite.CondensedFreeLinearization.generator A.toMon _ S x))
  simpa only [basis, InternalBar.generator, Profinite.CondensedFreeLinearization.generator,
    hx] using hh

/-- Existence and generator detection give the unique normalized deletion cochain map.
Source: character-lift calculation, steps 1--2
(blueprint: lem-sfb-internal-bar-character-deletion). -/
theorem exists_unique_deletion (D : Resolution A.toMon G) (a : Character A G) :
    ∃! L : complex D ⟶ (complex D)⟦(1 : ℤ)⟧, IsLift D a L := by
  obtain ⟨L, hL⟩ := exists_deletion D a
  exact ⟨L, hL, fun K hK ↦ deletion_unique D a K L hK hL⟩

end Profinite.CondensedAction.InternalBarCharacter
