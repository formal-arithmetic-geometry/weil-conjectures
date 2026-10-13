/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Affineness of a morphism is local on the target

`AlgebraicGeometry.isAffineHom_tfae`: a morphism `f : X ⟶ Y` is affine if and only if the
preimage of every affine open of `Y` is affine, if and only if there is a cover of `Y` by affine
opens with affine preimages (Stacks Project Tag 01S8).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **Affineness is local on the target** (Stacks Project Tag 01S8): for a morphism of schemes
`f : X ⟶ Y` the following are equivalent:
1. `f` is affine;
2. the preimage of every affine open of `Y` is affine;
3. there is a cover of `Y` by affine opens whose preimages are affine.
(blueprint: `pqf-lem-affine-local-target`; the definition `pqf-def-affine-morphism` is
`AlgebraicGeometry.IsAffineHom`) -/
@[stacks 01S8]
theorem isAffineHom_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
    List.TFAE [IsAffineHom f, ∀ U : Y.Opens, IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U),
      ∃ (ι : Type u) (U : ι → Y.affineOpens), ⨆ i, (U i : Y.Opens) = ⊤ ∧
        ∀ i, IsAffineOpen (f ⁻¹ᵁ (U i : Y.Opens))] := by
  tfae_have 1 → 2 := fun _ U hU ↦ hU.preimage f
  tfae_have 2 → 3 := fun H ↦ ⟨Y.affineOpens, id, by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩, fun U ↦ H U U.2⟩
  tfae_have 3 → 1 := fun ⟨ι, U, hU, H⟩ ↦
    (HasAffineProperty.iff_of_iSup_eq_top (P := @IsAffineHom) U hU).mpr H
  tfae_finish

end AlgebraicGeometry
