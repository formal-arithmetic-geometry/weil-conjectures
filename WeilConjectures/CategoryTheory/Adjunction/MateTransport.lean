/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

/-!
# Detecting invertibility of a base change map after restriction

Let `adj : F ⊣ G` and `adj' : F' ⊣ G'` be adjunctions, with `F : D ⥤ C` and `F' : D' ⥤ C'`, let
`adj_D : N_D ⊣ R_D` and `adj_C : N_C ⊣ R_C` be adjunctions with `N_D : D ⥤ D'` and
`N_C : C ⥤ C'`, and let `α : N_D ⋙ F' ≅ F ⋙ N_C`. Its mate `β : N_D (G M) ⟶ G' (N_C M)` is the
*base change map*. Write `γ : F (R_D P) ⟶ R_C (F' P)` for the mate of `α⁻¹`.

Suppose that the monads `N_D ⋙ R_D` and `N_C ⋙ R_C` are identified with endofunctors `T_D` and
`T_C` (for instance tensor products with a fixed object), and that `a : F (T_D X) ⟶ T_C (F X)`
corresponds to `γ` followed by `R_C α` under these identifications. Then `R_D β` is, up to
isomorphisms, the mate `G (T_D M) ⟶ T_C (G M)` of `a`. Hence `β` is an isomorphism at `M` as
soon as `R_D` reflects isomorphisms and the mate of `a` is an isomorphism at `M`.

This applies to derived extension of scalars `N = - ⊗ᴸ_R S` along the derived pullback `F = Lg^*`
and the derived direct image `G = Rg_*`: restricted back to `R`, extension of scalars is the
tensor product with `S`, and the mate of `a` is the projection map of `Rg_*` at `S`.

## Main results

- `CategoryTheory.Adjunction.map_mateEquiv_app_comp_mateEquiv_app`: the comparison of `R_D β`
  with the mate of `a`.
- `CategoryTheory.Adjunction.isIso_mateEquiv_app_of_isIso_mateEquiv_app`: the criterion for `β`
  to be an isomorphism.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) {F' : D' ⥤ C'} {G' : C' ⥤ D'} (adj' : F' ⊣ G')
  {N_D : D ⥤ D'} {N_C : C ⥤ C'} {R_D : D' ⥤ D} {R_C : C' ⥤ C}
  (adj_D : N_D ⊣ R_D) (adj_C : N_C ⊣ R_C) (α : N_D ⋙ F' ≅ F ⋙ N_C)
  {T_D : D ⥤ D} {T_C : C ⥤ C} (ϑ_D : T_D ⟶ N_D ⋙ R_D) (ϑ_C : T_C ⟶ N_C ⋙ R_C)
  (a : T_D ⋙ F ⟶ F ⋙ T_C)

/-- `R_D` of the base change map `β : N_D (G M) ⟶ G' (N_C M)`, the mate of `α`, compared with the
mate `G (T_D M) ⟶ T_C (G M)` of a natural transformation `a : F (T_D X) ⟶ T_C (F X)` which
corresponds to `γ` followed by `R_C α` through `ϑ_D : T_D ⟶ N_D ⋙ R_D` and
`ϑ_C : T_C ⟶ N_C ⋙ R_C`, `γ` being the mate of `α⁻¹`. The last arrow is the iterated mate of
`α⁻¹`, an isomorphism. -/
lemma map_mateEquiv_app_comp_mateEquiv_app
    (h : ∀ X, F.map (ϑ_D.app X) ≫ (mateEquiv adj_D adj_C α.inv).app (N_D.obj X) ≫
      R_C.map (α.hom.app X) = a.app X ≫ ϑ_C.app (F.obj X)) (M : C) :
    ϑ_D.app (G.obj M) ≫ R_D.map ((mateEquiv adj adj' α.hom).app M) ≫
        (mateEquiv adj' adj (mateEquiv adj_D adj_C α.inv)).app (N_C.obj M) =
      (mateEquiv adj adj a).app M ≫ G.map (ϑ_C.app M) := by
  apply (adj.homEquiv _ _).symm.injective
  have hκ := mateEquiv_counit adj' adj (mateEquiv adj_D adj_C α.inv) (N_C.obj M)
  have hβ := mateEquiv_counit adj adj' α.hom M
  have hγ := (mateEquiv adj_D adj_C α.inv).naturality ((mateEquiv adj adj' α.hom).app M)
  have ha := mateEquiv_counit adj adj a M
  have hϑ := ϑ_C.naturality (adj.counit.app M)
  dsimp at hκ hβ hγ ha hϑ
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [hκ, reassoc_of% hγ, ← R_C.map_comp, hβ, R_C.map_comp, reassoc_of% (h (G.obj M)),
    adj.counit_naturality, reassoc_of% ha, hϑ]

include adj' adj_C in
/-- **Invertibility of the base change map after restriction.** With the notation of
`CategoryTheory.Adjunction.map_mateEquiv_app_comp_mateEquiv_app`, if `ϑ_D` and `ϑ_C` are
isomorphisms, `R_D` reflects isomorphisms and the mate `G (T_D M) ⟶ T_C (G M)` of `a` is an
isomorphism at `M`, then so is the base change map `N_D (G M) ⟶ G' (N_C M)`. -/
theorem isIso_mateEquiv_app_of_isIso_mateEquiv_app [IsIso ϑ_D] [IsIso ϑ_C]
    [R_D.ReflectsIsomorphisms]
    (h : ∀ X, F.map (ϑ_D.app X) ≫ (mateEquiv adj_D adj_C α.inv).app (N_D.obj X) ≫
      R_C.map (α.hom.app X) = a.app X ≫ ϑ_C.app (F.obj X)) (M : C)
    [IsIso ((mateEquiv adj adj a).app M)] :
    IsIso ((mateEquiv adj adj' α.hom).app M) := by
  have : IsIso (mateEquiv adj' adj (mateEquiv adj_D adj_C α.inv)) :=
    isIso_mateEquiv_mateEquiv adj_D adj_C α.symm adj adj'
  have e := map_mateEquiv_app_comp_mateEquiv_app adj adj' adj_D adj_C α ϑ_D ϑ_C a h M
  have : IsIso (ϑ_D.app (G.obj M) ≫ R_D.map ((mateEquiv adj adj' α.hom).app M) ≫
      (mateEquiv adj' adj (mateEquiv adj_D adj_C α.inv)).app (N_C.obj M)) := by
    rw [e]
    infer_instance
  have : IsIso (R_D.map ((mateEquiv adj adj' α.hom).app M) ≫
      (mateEquiv adj' adj (mateEquiv adj_D adj_C α.inv)).app (N_C.obj M)) :=
    IsIso.of_isIso_comp_left (ϑ_D.app (G.obj M)) _
  have : IsIso (R_D.map ((mateEquiv adj adj' α.hom).app M)) :=
    IsIso.of_isIso_comp_right _
      ((mateEquiv adj' adj (mateEquiv adj_D adj_C α.inv)).app (N_C.obj M))
  exact isIso_of_reflects_iso _ R_D

end CategoryTheory.Adjunction
