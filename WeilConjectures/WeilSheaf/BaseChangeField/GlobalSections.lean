/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.BaseChangeField.Comparison
public import WeilConjectures.WeilSheaf.Stalk

/-!
# The Frobenius of global sections under transport and iteration

For a pro-étale sheaf `G` on a scheme `Z` with a morphism `φ : g_* G ⟶ G` along an
endomorphism `g` of `Z`, the global sections `Γ(Z, G)` carry the endomorphism

`Γ(Z, G) ≅ Γ(Z, g_* G) --Γ(φ)--> Γ(Z, G)`

(`AlgebraicGeometry.ProEtale.globalSectionsStr`); for `g = Fr⁻¹` and `φ` a Weil structure this
is the Frobenius of the global sections of a Weil sheaf
(`AlgebraicGeometry.WeilSheaf.globalSections`). This file shows that it is natural
(`AlgebraicGeometry.ProEtale.globalSectionsStr_naturality`), multiplicative under composition of
the endomorphisms (`AlgebraicGeometry.ProEtale.globalSectionsStr_comp`), trivial for the identity
(`AlgebraicGeometry.ProEtale.globalSectionsStr_id`), and invariant under transport along a
morphism `θ` (`AlgebraicGeometry.ProEtale.globalSectionsStr_transport`). Consequently the
endomorphism of the iterated Weil structure `φ_m` is the `m`-th power of that of `φ`
(`AlgebraicGeometry.ProEtaleWeilSheaf.globalSectionsStr_frobeniusPowIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

noncomputable section

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]


/-- The endomorphism `Γ(Z, G) ≅ Γ(Z, g_* G) --Γ(φ)--> Γ(Z, G)` of the global sections of a
pro-étale sheaf `G` with a morphism `φ : g_* G ⟶ G`. -/
def globalSectionsStr {Z : Scheme.{u}} (g : Z ⟶ Z) {G : Sheaf (Scheme.ProEt.topology Z)
    (WeilCoefficients.{u} l)} (φ : (g)_*[WeilCoefficients.{u} l].obj G ⟶ G) :
    (Sheaf.Γ (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)).obj G ⟶ (Sheaf.Γ (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)).obj G :=
  (globalSectionsLowerStarIso _ g).inv.app G ≫ (Sheaf.Γ (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)).map φ

variable {Z : Scheme.{u}}

/-- The endomorphism of the global sections is natural. -/
lemma globalSectionsStr_naturality (g : Z ⟶ Z) {G G' : Sheaf (Scheme.ProEt.topology Z)
    (WeilCoefficients.{u} l)} {φ : (g)_*[WeilCoefficients.{u} l].obj G ⟶ G}
    {φ' : (g)_*[WeilCoefficients.{u} l].obj G' ⟶ G'} (f : G ⟶ G')
    (hf : (g)_*[WeilCoefficients.{u} l].map f ≫ φ' = φ ≫ f) :
    (Sheaf.Γ (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)).map f ≫ globalSectionsStr g φ' = globalSectionsStr g φ ≫ (Sheaf.Γ (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)).map f := by
  have n := (globalSectionsLowerStarIso (WeilCoefficients.{u} l) g).inv.naturality f
  simp only [Functor.comp_map] at n
  rw [globalSectionsStr, globalSectionsStr, reassoc_of% n, Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, hf]

/-- The endomorphism of the global sections for `g₃ = g₂ ≫ g₁` and the composite
`g₃_* G ≅ g₁_* g₂_* G --g₁_* φ₂--> g₁_* G --φ₁--> G` is the composite of those for `φ₂` and
`φ₁`. -/
lemma globalSectionsStr_comp (g₁ g₂ g₃ : Z ⟶ Z) (h : g₃ = g₂ ≫ g₁)
    {G : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)}
    (φ₁ : (g₁)_*[WeilCoefficients.{u} l].obj G ⟶ G)
    (φ₂ : (g₂)_*[WeilCoefficients.{u} l].obj G ⟶ G) :
    globalSectionsStr g₃ ((lowerStarCongr _ h).hom.app G ≫ (lowerStarComp _ g₂ g₁).inv.app G ≫
        (g₁)_*[WeilCoefficients.{u} l].map φ₂ ≫ φ₁) =
      globalSectionsStr g₂ φ₂ ≫ globalSectionsStr g₁ φ₁ := by
  have e₁ := globalSectionsLowerStarIso_comp (WeilCoefficients.{u} l) g₂ g₁ G
  have e₂ := globalSectionsLowerStarIso_congr (WeilCoefficients.{u} l) h G
  have n := (globalSectionsLowerStarIso (WeilCoefficients.{u} l) g₁).inv.naturality φ₂
  simp only [Functor.comp_map] at n
  have e₁' : (globalSectionsLowerStarIso (WeilCoefficients.{u} l) (g₂ ≫ g₁)).hom.app G =
      (Sheaf.Γ _ _).map ((lowerStarComp _ g₂ g₁).inv.app G) ≫
        (globalSectionsLowerStarIso (WeilCoefficients.{u} l) g₁).hom.app ((g₂)_*[_].obj G) ≫
          (globalSectionsLowerStarIso (WeilCoefficients.{u} l) g₂).hom.app G := by
    rw [← e₁, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have key : (globalSectionsLowerStarIso (WeilCoefficients.{u} l) g₃).inv.app G ≫
      (Sheaf.Γ _ _).map ((lowerStarCongr _ h).hom.app G) ≫
        (Sheaf.Γ _ _).map ((lowerStarComp _ g₂ g₁).inv.app G) =
      (globalSectionsLowerStarIso (WeilCoefficients.{u} l) g₂).inv.app G ≫
        (globalSectionsLowerStarIso (WeilCoefficients.{u} l) g₁).inv.app ((g₂)_*[_].obj G) := by
    rw [← cancel_epi ((globalSectionsLowerStarIso (WeilCoefficients.{u} l) g₃).hom.app G),
      Iso.hom_inv_id_app_assoc, ← e₂, e₁']
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  simp only [globalSectionsStr, Functor.map_comp, Category.assoc]
  rw [reassoc_of% n, reassoc_of% key]

/-- The endomorphism of the global sections for `g = 𝟙` and the identification `𝟙_* G ≅ G` is
the identity. -/
lemma globalSectionsStr_id (g : Z ⟶ Z) (h : g = 𝟙 Z)
    (G : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) :
    globalSectionsStr g ((lowerStarCongr _ h).hom.app G ≫ (lowerStarId _ Z).hom.app G) = 𝟙 _ := by
  have e₁ := globalSectionsLowerStarIso_congr (WeilCoefficients.{u} l) h G
  rw [globalSectionsLowerStarIso_id] at e₁
  rw [globalSectionsStr, Functor.map_comp, e₁, Iso.inv_hom_id_app]

/-- The endomorphism of the global sections is invariant under transport along a morphism `θ`
with `θ ≫ F' = F ≫ θ`: the global sections of `θ_* G`, with
`F'_* θ_* G ≅ θ_* F_* G --θ_* φ--> θ_* G`, are those of `G`, with `φ`. -/
lemma globalSectionsStr_transport {Z' : Scheme.{u}} (θ : Z ⟶ Z') (F : Z ⟶ Z) (F' : Z' ⟶ Z')
    (h : θ ≫ F' = F ≫ θ) {G : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)}
    (φ : (F)_*[WeilCoefficients.{u} l].obj G ⟶ G) :
    globalSectionsStr F' ((lowerStarComp _ θ F').hom.app G ≫ (lowerStarCongr _ h).hom.app G ≫
        (lowerStarComp _ F θ).inv.app G ≫ (θ)_*[WeilCoefficients.{u} l].map φ) ≫
        (globalSectionsLowerStarIso _ θ).hom.app G =
      (globalSectionsLowerStarIso _ θ).hom.app G ≫ globalSectionsStr F φ := by
  have e₁ := globalSectionsLowerStarIso_comp (WeilCoefficients.{u} l) θ F' G
  have e₂ := globalSectionsLowerStarIso_congr (WeilCoefficients.{u} l) h G
  have e₃ := globalSectionsLowerStarIso_comp (WeilCoefficients.{u} l) F θ G
  have n := (globalSectionsLowerStarIso (WeilCoefficients.{u} l) θ).hom.naturality φ
  simp only [Functor.comp_map] at n
  simp only [globalSectionsStr, Functor.map_comp, Category.assoc]
  rw [n]
  rw [← cancel_epi ((globalSectionsLowerStarIso (WeilCoefficients.{u} l) F').hom.app _),
    Iso.hom_inv_id_app_assoc]
  have e₃' : (Sheaf.Γ _ _).map ((lowerStarComp _ F θ).inv.app G) ≫
      (globalSectionsLowerStarIso (WeilCoefficients.{u} l) θ).hom.app ((F)_*[_].obj G) =
        (globalSectionsLowerStarIso (WeilCoefficients.{u} l) (F ≫ θ)).hom.app G ≫
          (globalSectionsLowerStarIso (WeilCoefficients.{u} l) F).inv.app G := by
    rw [← cancel_epi ((Sheaf.Γ _ _).map ((lowerStarComp _ F θ).hom.app G)),
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, reassoc_of% e₃, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [reassoc_of% e₃', reassoc_of% e₂, reassoc_of% e₁]

end AlgebraicGeometry.ProEtale
