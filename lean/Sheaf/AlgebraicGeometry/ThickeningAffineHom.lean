/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.ThickeningAffineScheme

/-! Affineness and arbitrary thickenings.

Source: Stacks Project, More on Morphisms, Lemma 37.3.1 (Tag 09ZV), part (1)
(blueprint: lem-weil-pbc-thickening-affine-morphism).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Affineness of a morphism is preserved when both source and target are replaced
by arbitrary thickenings.  This is the affine part of More on Morphisms, Lemma
37.3.1 (1); it follows by applying the affine-open correspondence of Tag 06AD
to affine opens of the target and their inverse images.
Source: Stacks Project, Tag 09ZV (1), using Tag 06AD.
(blueprint: lem-weil-pbc-thickening-affine-morphism).
Proof: For an affine open V of S', the preimage under i_S is affine since a
closed immersion is affine. Its preimage under f is affine. Commutativity
identifies this with i_X's preimage of f'⁻¹(V). The restriction of i_X to
that open is a closed immersion, and is surjective: lift a point using i_X's
surjectivity; the lift belongs to the preimage open. Hence it is a thickening
with affine source. Tag 06AD makes f'⁻¹(V) affine, proving f' affine. -/
theorem isAffineHom_of_thickenings {S S' X X' : Scheme.{u}}
    (i_S : S ⟶ S') (i_X : X ⟶ X') (f' : X' ⟶ S') (f : X ⟶ S)
    (hS : IsThickening i_S) (hX : IsThickening i_X)
    (hcomm : i_X ≫ f' = f ≫ i_S) [IsAffineHom f] : IsAffineHom f' := by
  have : IsClosedImmersion i_S := hS.1
  have : IsClosedImmersion i_X := hX.1
  have : Surjective i_X := hX.2
  constructor
  intro V hV
  have hpre : IsAffineOpen (i_X ⁻¹ᵁ (f' ⁻¹ᵁ V)) := by
    rw [← Scheme.Hom.comp_preimage, hcomm, Scheme.Hom.comp_preimage]
    exact (hV.preimage i_S).preimage f
  have : IsAffine (i_X ⁻¹ᵁ (f' ⁻¹ᵁ V)).toScheme := hpre
  have hsurj : Surjective (i_X ∣_ (f' ⁻¹ᵁ V)) := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := i_X.surjective y.1
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change i_X x ∈ f' ⁻¹ᵁ V
      simp only [hx]
      exact y.2
    · apply Subtype.ext
      simpa only [morphismRestrict_base_coe] using hx
  exact isAffine_of_isThickening (i_X ∣_ (f' ⁻¹ᵁ V)) ⟨inferInstance, hsurj⟩

end AlgebraicGeometry
