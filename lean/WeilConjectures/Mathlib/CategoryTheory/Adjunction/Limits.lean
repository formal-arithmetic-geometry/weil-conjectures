/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Left adjoints with invertible counit and comparison maps of colimits

Let `F ⊣ G` be an adjunction whose counit is an isomorphism (i.e. `G` is fully faithful), and
let `Y : J ⥤ D` be a diagram with a colimit cocone `c`. The comparison map
`colim (Y ⋙ G) ⟶ G.obj c.pt` need not be an isomorphism, but `F` sends it to an isomorphism
as soon as `F` preserves the colimit of `Y ⋙ G`.

## Main results

- `Adjunction.isIso_map_colimitDesc_mapCocone`.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Adjunction

open Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C}

/-- If the counit of `F ⊣ G` is an isomorphism and `F` preserves the colimit of `Y ⋙ G`, then
`F` sends the comparison map `colim (Y ⋙ G) ⟶ G.obj c.pt` to an isomorphism. -/
lemma isIso_map_colimitDesc_mapCocone (adj : F ⊣ G) [IsIso adj.counit] {J : Type u₃}
    [Category.{v₃} J] {Y : J ⥤ D} [HasColimit (Y ⋙ G)] [PreservesColimit (Y ⋙ G) F]
    {c : Cocone Y} (hc : IsColimit c) :
    IsIso (F.map (colimit.desc (Y ⋙ G) (G.mapCocone c))) := by
  have hF := isColimitOfPreserves F (colimit.isColimit (Y ⋙ G))
  have hc' := (IsColimit.precomposeHomEquiv
    (asIso (Functor.whiskerLeft Y adj.counit)) c).symm hc
  have : F.map (colimit.desc _ (G.mapCocone c)) ≫ adj.counit.app c.pt =
      (hF.coconePointUniqueUpToIso hc').hom :=
    hF.hom_ext fun j ↦ by
      rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
      dsimp
      rw [← F.map_comp_assoc, colimit.ι_desc]
      exact adj.counit.naturality (c.ι.app j)
  rw [← isIso_comp_right_iff _ (adj.counit.app c.pt), this]
  infer_instance

end CategoryTheory.Adjunction
