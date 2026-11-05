/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.KunnethMap

/-!

# Künneth maps as transposes

Let `F ⊣ G` be an adjunction between monoidal categories with `F` oplax monoidal, and let
`μ : G M ⊗ G N ⟶ G (M ⊗ N)` be a lax tensor map whose transpose is the tensor product of the
counits. A Künneth map `(b₁ ⊗ b₂) ≫ μ` is then the transpose of `F (U₁ ⊗ U₂) ⟶ F U₁ ⊗ F U₂`
followed by the tensor product of the transposes of the `bᵢ`
(`CategoryTheory.Adjunction.tensorHom_comp_eq_homEquiv_δ`). Such transposes are compatible with
the restriction of `F ⊣ G` to full monoidal subcategories
(`CategoryTheory.Adjunction.ι_map_homEquiv_δ_tensorHom_restrictFullyFaithful`).

-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

section Restrict

variable {P : ObjectProperty C} [P.IsMonoidal] {Q : ObjectProperty D} [Q.IsMonoidal]
  {F' : D ⥤ C} [F'.Monoidal] {G' : C ⥤ D} (adj' : F' ⊣ G')
  (hF : ∀ X : Q.FullSubcategory, P (F'.obj X.obj)) (hG : ∀ X : P.FullSubcategory, Q (G'.obj X.obj))

end Restrict

end CategoryTheory.Adjunction
