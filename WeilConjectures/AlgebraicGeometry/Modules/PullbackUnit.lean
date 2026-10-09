/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The unit of the pullback-pushforward adjunction on sections

For a morphism of schemes `f : Y ⟶ X` and an `𝒪_X`-module `M`, the unit of the adjunction
`f^* ⊣ f_*` gives maps `Γ(M, U) ⟶ Γ(f^* M, f ⁻¹ᵁ U)`. We record how these maps behave under
composition of morphisms and under restriction along open immersions, and that morphisms out of
`f^* M` are determined by their values on the image of these maps.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- The unit of `pullback f ⊣ pushforward f`, on sections. -/
noncomputable abbrev pullbackUnit (f : Y ⟶ X) (M : X.Modules) :
    M ⟶ (pushforward f).obj ((pullback f).obj M) :=
  (pullbackPushforwardAdjunction f).unit.app M

set_option backward.isDefEq.respectTransparency.types false in
/-- The units of the pullback-pushforward adjunctions compose, up to `pullbackComp`. -/
lemma pullbackUnit_comp_app (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    (pullbackUnit (g ≫ f) M).app U ≫ ((pullbackComp g f).inv.app M).app ((g ≫ f) ⁻¹ᵁ U) =
      (pullbackUnit f M).app U ≫ (pullbackUnit g ((pullback f).obj M)).app (f ⁻¹ᵁ U) := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction f).comp
    (pullbackPushforwardAdjunction g)) (pullbackPushforwardAdjunction (g ≫ f))
    (pullbackComp g f).inv M
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  have := congr_arg (fun φ ↦ Hom.app φ U) h
  simpa using this.symm

lemma pullbackUnit_comp_app_apply (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (m : Γ(M, U)) :
    ((pullbackComp g f).inv.app M).app ((g ≫ f) ⁻¹ᵁ U) ((pullbackUnit (g ≫ f) M).app U m) =
      (pullbackUnit g ((pullback f).obj M)).app (f ⁻¹ᵁ U) ((pullbackUnit f M).app U m) :=
  congr($(pullbackUnit_comp_app g f M U) m)

/-- Two morphisms out of `f^* M` agree if they agree on the image of the unit. -/
lemma pullback_hom_ext (f : Y ⟶ X) {M : X.Modules} {P : Y.Modules}
    {φ ψ : (pullback f).obj M ⟶ P}
    (h : ∀ (U : X.Opens) (m : Γ(M, U)),
      φ.app (f ⁻¹ᵁ U) ((pullbackUnit f M).app U m) = ψ.app (f ⁻¹ᵁ U) ((pullbackUnit f M).app U m)) :
    φ = ψ := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).injective
  ext U m
  simp only [Adjunction.homEquiv_unit, Hom.comp_app, pushforward_map_app]
  exact h U m

section OpenImmersion

variable (j : Y ⟶ X) [IsOpenImmersion j]

set_option backward.isDefEq.respectTransparency.types false in
/-- Along an open immersion, the unit of the pullback-pushforward adjunction is the unit of the
restriction adjunction followed by the comparison `restrictFunctorIsoPullback`. -/
lemma pullbackUnit_eq_of_isOpenImmersion (M : X.Modules) :
    pullbackUnit j M = (restrictAdjunction j).unit.app M ≫
      (pushforward j).map ((restrictFunctorIsoPullback j).hom.app M) :=
  ((restrictAdjunction j).unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction j) M).symm

/-- Along an open immersion, the unit of the pullback-pushforward adjunction is bijective on
sections over opens contained in the range. -/
lemma bijective_pullbackUnit_app_of_isOpenImmersion (M : X.Modules) {U : X.Opens}
    (hU : U ≤ j.opensRange) : Function.Bijective ((pullbackUnit j M).app U) := by
  rw [pullbackUnit_eq_of_isOpenImmersion, Hom.comp_app, restrictAdjunction_unit_app_app]
  have : j ''ᵁ (j ⁻¹ᵁ U) = U := le_antisymm (j.image_preimage_le U) (by
    intro x hx
    obtain ⟨y, rfl⟩ := hU hx
    exact ⟨y, hx, rfl⟩)
  have : IsIso (homOfLE (j.image_preimage_le U)) :=
    ⟨homOfLE (by rw [this]), Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  exact (ConcreteCategory.bijective_of_isIso
    (((pushforward j).map ((restrictFunctorIsoPullback j).hom.app M)).app U)).comp
    (ConcreteCategory.bijective_of_isIso (M.presheaf.map (homOfLE (j.image_preimage_le U)).op))

end OpenImmersion

end AlgebraicGeometry.Scheme.Modules
