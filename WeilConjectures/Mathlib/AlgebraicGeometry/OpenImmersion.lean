/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Claude
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Complements on open immersions of schemes

The `MorphismProperty.RespectsRight` instance for open immersions of schemes, and the
compatibility of the stalk map of an open immersion with the identification
`Γ(W, f(U)) ≅ Γ(Y, U)` of `AlgebraicGeometry.Scheme.Hom.appIso`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

instance : MorphismProperty.RespectsRight @IsOpenImmersion @IsOpenImmersion :=
  ⟨fun i hi f hf ↦ by
    have : IsOpenImmersion i := hi
    have : IsOpenImmersion f := hf
    infer_instance⟩

/-- The stalk map of an open immersion `f` sends the germ of the section corresponding to
`a ∈ Γ(Y, U)` under `Γ(W, f(U)) ≅ Γ(Y, U)` to the germ of `a`. -/
lemma Scheme.Hom.stalkMap_germ_appIso_inv {Y W : Scheme.{u}} (f : Y ⟶ W) [IsOpenImmersion f]
    (y : Y) (U : Y.Opens) (hy : y ∈ U) (a : Γ(Y, U)) :
    f.stalkMap y (W.presheaf.germ (f ''ᵁ U) (f y) ⟨y, hy, rfl⟩ ((f.appIso U).inv a)) =
      Y.presheaf.germ U y hy a := by
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply]
  exact Y.presheaf.germ_res_apply _ y _ a

end AlgebraicGeometry
