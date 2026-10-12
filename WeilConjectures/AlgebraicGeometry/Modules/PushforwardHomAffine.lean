/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.PushforwardHom

/-!
# Morphisms out of a pushforward of the structure sheaf over an affine open

Let `f : X ⟶ Y` be a morphism of schemes, `V` an affine open of `Y` with `f⁻¹V` affine, and `N`
an `𝒪_Y`-module. A morphism `(f_* 𝒪_X)|_V ⟶ N|_V` is determined by its value on the sections over
`V`: over a basic open `D(r) ⊆ V` the sections of `f_* 𝒪_X` are the localization of
`Γ(X, f⁻¹V)` at `f^♯ r`, on which the morphism is determined by linearity, as `r` is a unit there;
and the basic opens of `V` cover every open of `V`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {N : Y.Modules}

/-- A morphism `(f_* 𝒪_X)|_V ⟶ N|_V`, for `V` and `f⁻¹V` affine, is determined by its value on
the sections over `V`. -/
lemma restrictOver_pushforward_unit_hom_ext {V : Y.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (f ⁻¹ᵁ V))
    {χ₁ χ₂ : (PresheafOfModules.restrictOver Y.sheaf.obj V).obj
        ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val ⟶
      (PresheafOfModules.restrictOver Y.sheaf.obj V).obj N.val}
    (h : χ₁.app (op (Over.mk (𝟙 V))) = χ₂.app (op (Over.mk (𝟙 V)))) : χ₁ = χ₂ :=
  sorry

end AlgebraicGeometry.Scheme.Modules
