/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.Category

/-!
# A formal cube lemma for the reduction square of the pullbacks

The reduction square for the pullbacks (blueprint `det-sp-purity-coefficient-change`,
`ProEtale.CondensedRing.etaleReductionUpperStarIso_restrictScalars`) is checked after composing
with an invertible base change map `Res Rν_* ⟶ Rν_* Res`: there it splits into a statement on the
étale side (the base change maps `Lf^* Rν_* ⟶ Rν_* Lf^*` are compatible with restriction of
scalars) and a statement on the pro-étale side. This file contains the formal part of this
splitting, `CategoryTheory.map_comp_app_comp_map_eq_of_cube`.
-/

@[expose] public section

open CategoryTheory Category

namespace CategoryTheory

/-- **A formal cube lemma**: let `u₁ = bc₁ ≫ ν(w₁)` and `u₀ = bc₀ ≫ ν(w₀)` be composites of base
change maps `bc : ν ⋙ F ⟶ G ⋙ ν` with morphisms `w`, and let `T_Y`, `T_Z` be morphisms whose
composites with the maps `ω : ν ⋙ Res ⟶ Res ⋙ ν` are `ν(τ_Y)`, `ν(τ_Z)`. If `ω_Z` is a
monomorphism, the base change maps are compatible with the commutations `LUR`, `LURp` of `Res`
with `F`, `G` (`hA`) and `τ_Y`, `τ_Z` are intertwined by `w₁`, `w₀` and `LURp` (`hB`), then
`T_Y`, `T_Z` are intertwined by `u₁`, `u₀` and `LUR`. -/
theorem map_comp_app_comp_map_eq_of_cube
    {EY₁ EY₀ EZ₁ EZ₀ PY₁ PY₀ PZ₁ PZ₀ : Type*} [Category EY₁] [Category EY₀] [Category EZ₁]
    [Category EZ₀] [Category PY₁] [Category PY₀] [Category PZ₁] [Category PZ₀]
    {F₁ : EY₁ ⥤ EZ₁} {F₀ : EY₀ ⥤ EZ₀} {ResY : EY₀ ⥤ EY₁} {ResZ : EZ₀ ⥤ EZ₁}
    {νY₁ : PY₁ ⥤ EY₁} {νY₀ : PY₀ ⥤ EY₀} {νZ₁ : PZ₁ ⥤ EZ₁} {νZ₀ : PZ₀ ⥤ EZ₀}
    {ResPY : PY₀ ⥤ PY₁} {ResPZ : PZ₀ ⥤ PZ₁} {G₁ : PY₁ ⥤ PZ₁} {G₀ : PY₀ ⥤ PZ₀}
    (bc₁ : νY₁ ⋙ F₁ ⟶ G₁ ⋙ νZ₁) (bc₀ : νY₀ ⋙ F₀ ⟶ G₀ ⋙ νZ₀)
    (ωY : νY₀ ⋙ ResY ⟶ ResPY ⋙ νY₁) (ωZ : νZ₀ ⋙ ResZ ⟶ ResPZ ⋙ νZ₁)
    (LUR : ResY ⋙ F₁ ⟶ F₀ ⋙ ResZ) (LURp : ResPY ⋙ G₁ ⟶ G₀ ⋙ ResPZ)
    {p₁ : PY₁} {p₀ : PY₀} {q₁ : PZ₁} {q₀ : PZ₀}
    (TY : νY₁.obj p₁ ⟶ ResY.obj (νY₀.obj p₀)) (TZ : νZ₁.obj q₁ ⟶ ResZ.obj (νZ₀.obj q₀))
    (u₁ : F₁.obj (νY₁.obj p₁) ⟶ νZ₁.obj q₁) (u₀ : F₀.obj (νY₀.obj p₀) ⟶ νZ₀.obj q₀)
    (τY : p₁ ⟶ ResPY.obj p₀) (τZ : q₁ ⟶ ResPZ.obj q₀) (w₁ : G₁.obj p₁ ⟶ q₁)
    (w₀ : G₀.obj p₀ ⟶ q₀) [Mono (ωZ.app q₀)]
    (hu₁ : u₁ = bc₁.app p₁ ≫ νZ₁.map w₁) (hu₀ : u₀ = bc₀.app p₀ ≫ νZ₀.map w₀)
    (hTY : TY ≫ ωY.app p₀ = νY₁.map τY) (hTZ : TZ ≫ ωZ.app q₀ = νZ₁.map τZ)
    (hA : F₁.map (ωY.app p₀) ≫ bc₁.app (ResPY.obj p₀) ≫ νZ₁.map (LURp.app p₀) =
      LUR.app (νY₀.obj p₀) ≫ ResZ.map (bc₀.app p₀) ≫ ωZ.app (G₀.obj p₀))
    (hB : G₁.map τY ≫ LURp.app p₀ ≫ ResPZ.map w₀ = w₁ ≫ τZ) :
    F₁.map TY ≫ LUR.app (νY₀.obj p₀) ≫ ResZ.map u₀ = u₁ ≫ TZ := by
  subst hu₁ hu₀
  rw [← cancel_mono (ωZ.app q₀)]
  have hω := ωZ.naturality w₀
  have hbc := bc₁.naturality τY
  dsimp only [Functor.comp_map, Functor.comp_obj] at hω hbc
  simp only [assoc, hTZ, Functor.map_comp, hω]
  rw [reassoc_of% (hA.symm), ← F₁.map_comp_assoc, hTY, reassoc_of% hbc, ← νZ₁.map_comp,
    ← νZ₁.map_comp, hB, Functor.map_comp]

end CategoryTheory
