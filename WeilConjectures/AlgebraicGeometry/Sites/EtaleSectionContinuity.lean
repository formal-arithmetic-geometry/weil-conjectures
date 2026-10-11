/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Sections of étale sheaves over limits of étale schemes

Let `F` be an abelian étale sheaf on a scheme `X`.

For an étale morphism `t : T ⟶ X` the pullback `t^* F` is the restriction of `F` along the
functor `T_ét ⥤ X_ét` composing with `t`: the pullback of sections `pullSection t F` from an
étale `X`-scheme `V` to `V` itself, viewed as an étale `T`-scheme, is bijective
(`AlgebraicGeometry.Etale.bijective_pullSection_of_etale`).

Together with the continuity of sections at inverse limits
(`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`), this shows that for a
cofiltered system `(Dⱼ)` of quasi-compact quasi-separated étale `X`-schemes with affine
transition maps and with a terminal index, the sections of `F` over the `Dⱼ` have as colimit the
sections of the pullback of `F` to the limit `D` of the system
(`AlgebraicGeometry.Etale.exists_pullSection_eq_of_isLimit`,
`AlgebraicGeometry.Etale.exists_map_eq_zero_of_pullSection_eq_zero_of_isLimit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

section EtalePullback

variable {X T : Scheme.{u}} (t : T ⟶ X) (h : AlgebraicGeometry.Etale t)
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

set_option backward.isDefEq.respectTransparency false in
/-- For an étale `t`, the identification `t^* F ≅ j_t^* F` of the pullback with the restriction
along `T_ét ⥤ X_ét` sends the pullback `φ^* g` of a section `g` of `F` over `U` along
`φ : V ⟶ U` to the restriction of `g` along `φ`, viewed as a morphism of étale `X`-schemes. -/
lemma upperStarIsoLocalizationRestriction_hom_app_pullSection {V : T.Etale} {U : X.Etale}
    (φ : V.left ⟶ U.left) (hφ : φ ≫ U.hom = V.hom ≫ t) (g : F.obj.obj (op U)) :
    ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} t h).hom.app F).hom.app
        (op V) (pullSection t F φ hφ g) =
      F.obj.map (MorphismProperty.Over.homMk φ hφ :
        (MorphismProperty.Over.map ⊤ h).obj V ⟶ U).op g := by
  set e := Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} t h
  have h₁ := Adjunction.unit_leftAdjointUniq_hom_app
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t)
    (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} t h) F
  have h₂ := congrArg (fun α ↦ α.hom.app (op U) g) h₁
  have h₃ : (e.hom.app F).hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ t).obj U))
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app F).hom.app (op U) g) =
      F.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ t h trivial).counit.app U).op g :=
    h₂
  rw [pullSection, NatTrans.naturality_apply, h₃]
  change F.obj.map _ (F.obj.map _ g) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 3
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp [homToPullback]

include h in
/-- **Sections of the pullback along an étale morphism.** For an étale `t : T ⟶ X`, an étale
`T`-scheme `V`, an étale `X`-scheme `U` and an isomorphism `φ : V ⟶ U` over `X`, the pullback
of sections `pullSection t F φ : F(U) ⟶ (t^* F)(V)` is bijective. -/
lemma bijective_pullSection_of_etale {V : T.Etale} {U : X.Etale} (φ : V.left ⟶ U.left)
    [IsIso φ] (hφ : φ ≫ U.hom = V.hom ≫ t) :
    Function.Bijective (pullSection t F φ hφ) := by
  let ψ : (MorphismProperty.Over.map ⊤ h).obj V ⟶ U := MorphismProperty.Over.homMk φ hφ
  have : IsIso ψ := ⟨MorphismProperty.Over.homMk (inv φ)
      (by rw [IsIso.inv_comp_eq, hφ]; rfl),
    MorphismProperty.Over.Hom.ext (by simp [ψ]), MorphismProperty.Over.Hom.ext (by simp [ψ])⟩
  have h₁ : Function.Bijective (F.obj.map ψ.op) :=
    ConcreteCategory.bijective_of_isIso (F.obj.map ψ.op)
  have h₂ : Function.Bijective
      (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} t h).hom.app F).hom.app
        (op V)) :=
    ConcreteCategory.bijective_of_isIso (((sheafSections _ _).obj (op V)).map
      ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} t h).hom.app F))
  have h₃ : (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} t h).hom.app
      F).hom.app (op V)) ∘ pullSection t F φ hφ = F.obj.map ψ.op :=
    funext fun g ↦ upperStarIsoLocalizationRestriction_hom_app_pullSection t h F φ hφ g
  rw [← h₂.of_comp_iff', h₃]
  exact h₁

end EtalePullback

section Limit

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  {J : Type u} [SmallCategory J] [IsCofiltered J] (U : J ⥤ X.Etale)
  (c : Cone (U ⋙ Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X))
  (j₀ : J) (hj₀ : IsTerminal j₀) (t : c.pt ⟶ X) (ht : t = c.π.app j₀ ≫ (U.obj j₀).hom)

omit [IsCofiltered J] in
include hj₀ ht in
/-- The legs of a cone over a system of étale `X`-schemes with a terminal index are morphisms
over `X`. -/
lemma π_app_comp_hom_of_isTerminal (j : J) :
    c.π.app j ≫ (U.obj j).hom = (Scheme.Etale.mk (𝟙 c.pt)).hom ≫ t := by
  have h₁ : c.π.app j ≫ (U.map (hj₀.from j)).left = c.π.app j₀ := c.w (hj₀.from j)
  have h₂ : (U.map (hj₀.from j)).left ≫ (U.obj j₀).hom = (U.obj j).hom :=
    MorphismProperty.Over.w _
  rw [ht, ← h₁, Category.assoc, h₂]
  exact (Category.id_comp _).symm

end Limit

end AlgebraicGeometry.Etale
