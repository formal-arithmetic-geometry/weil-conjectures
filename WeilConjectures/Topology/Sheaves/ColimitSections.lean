/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Sections of colimits of sheaves, and the presheaf of locally constant maps

- `TopCat.Sheaf.colimitSectionsMap`: for a diagram `D` of sheaves with a colimit and an open `U`,
  the canonical map `colim_i D_i(U) → (colim D)(U)` (Stacks 009F).
- `TopCat.locallyConstantMapsPresheaf`: the presheaf `V ↦ {locally constant maps V → R}`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat

variable {X : TopCat.{u}} {C : Type*} [Category C]

/-- The canonical map `colim_i D_i(U) → (colim D)(U)` for a diagram of sheaves `D` and an open
`U`; its composite with the `i`-th coprojection is the component at `U` of the coprojection
`D_i → colim D`. (blueprint: `aux-directed-colimit-map`) -/
noncomputable def Sheaf.colimitSectionsMap {J : Type*} [Category J] (D : J ⥤ X.Sheaf C)
    [HasColimit D] (U : (Opens X)ᵒᵖ)
    [HasColimit (D ⋙ sheafToPresheaf _ C ⋙ (evaluation _ C).obj U)] :
    colimit (D ⋙ sheafToPresheaf _ C ⋙ (evaluation _ C).obj U) ⟶ (colimit D).obj.obj U :=
  colimit.post D (sheafToPresheaf _ C ⋙ (evaluation _ C).obj U)

@[reassoc (attr := simp)]
lemma Sheaf.ι_colimitSectionsMap {J : Type*} [Category J] (D : J ⥤ X.Sheaf C)
    [HasColimit D] (U : (Opens X)ᵒᵖ)
    [HasColimit (D ⋙ sheafToPresheaf _ C ⋙ (evaluation _ C).obj U)] (j : J) :
    colimit.ι (D ⋙ sheafToPresheaf _ C ⋙ (evaluation _ C).obj U) j ≫
      Sheaf.colimitSectionsMap D U = (colimit.ι D j).hom.app U :=
  colimit.ι_post _ _ _

variable (X) in
/-- The presheaf on `X` sending an open `V` to the set of locally constant maps `V → R`, with
restriction given by precomposition. (blueprint: `def-weil-pbc-locally-constant-maps-presheaf`) -/
@[simps!]
def locallyConstantMapsPresheaf (R : Type u) : X.Presheaf (Type u) where
  obj V := LocallyConstant V.unop R
  map {V W} i := ↾fun f ↦ f.comap ⟨fun x ↦ ⟨x.1, i.unop.le x.2⟩, by fun_prop⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end TopCat
