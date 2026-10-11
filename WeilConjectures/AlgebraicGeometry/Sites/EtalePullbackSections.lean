/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Sections of inverse images along étale morphisms

For an étale morphism `v : V ⟶ S`, the inverse image `v^* F` of an abelian étale sheaf `F` on `S`
is the restriction of `F` to the étale `V`-schemes, viewed as étale `S`-schemes
(`AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction`). Under this identification the
pullback `φ^* g` of a section `g` of `F` over an étale `S`-scheme `U` along an `S`-morphism
`φ : T ⟶ U` from an étale `V`-scheme `T` is the restriction of `g` along `φ`
(`AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction_pullSection`). In particular, if
`φ` is an isomorphism, then `g ↦ φ^* g` is bijective
(`AlgebraicGeometry.Etale.pullSection_bijective_of_isIso`).

We also record that `pullSection` is natural in the sheaf.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

section Naturality

variable {R T : Scheme.{u}} (t : T ⟶ R)

/-- `AlgebraicGeometry.Etale.pullSection` is natural in the sheaf. -/
lemma pullSection_naturality {G G' : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ψ : G ⟶ G') {V : T.Etale} {U : R.Etale} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ t) (g : G.obj.obj (op U)) :
    (((t)^*[AddCommGrpCat.{u + 1}]).map ψ).hom.app (op V) (pullSection t G φ hφ g) =
      pullSection t G' φ hφ (ψ.hom.app (op U) g) := by
  have h : (((t)^*[AddCommGrpCat.{u + 1}]).map ψ).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ t).obj U))
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app G).hom.app (op U) g) =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app G').hom.app (op U)
        (ψ.hom.app (op U) g) :=
    (congrArg (fun k ↦ k.hom.app (op U) g)
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.naturality ψ)).symm
  rw [pullSection, pullSection, ← h]
  exact NatTrans.naturality_apply (((t)^*[AddCommGrpCat.{u + 1}]).map ψ).hom _ _

end Naturality

section Etale

variable {S V : Scheme.{u}} (v : V ⟶ S) [hv : AlgebraicGeometry.Etale v]
  (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The `S`-morphism `T ⟶ U` of étale `S`-schemes given by an `S`-morphism `φ` from an étale
`V`-scheme `T`, viewed as an étale `S`-scheme. -/
noncomputable def etaleOverHom {T : V.Etale} {U : S.Etale} (φ : T.left ⟶ U.left)
    (hφ : φ ≫ U.hom = T.hom ≫ v) : (MorphismProperty.Over.map ⊤ hv).obj T ⟶ U :=
  MorphismProperty.Over.homMk φ hφ

/-- Under the identification of `v^* F` with the restriction of `F`, the pullback `φ^* g` of a
section `g` is the restriction of `g` along `φ`. -/
lemma upperStarIsoLocalizationRestriction_pullSection {T : V.Etale} {U : S.Etale}
    (φ : T.left ⟶ U.left) (hφ : φ ≫ U.hom = T.hom ≫ v) (g : F.obj.obj (op U)) :
    ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} v hv).hom.app F).hom.app
        (op T) (pullSection v F φ hφ g) = F.obj.map (etaleOverHom v φ hφ).op g := by
  set ι := (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} v hv).hom.app F
  have hu := congrArg (fun k ↦ k.hom.app (op U) g)
    (Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v)
      (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} v hv) F)
  change ι.hom.app _ (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).unit.app F).hom.app
    (op U) g) = F.obj.map ((MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ v hv
      trivial).counit.app U).op g at hu
  rw [pullSection, NatTrans.naturality_apply]
  erw [hu]
  change F.obj.map ((MorphismProperty.Over.map ⊤ hv).map (homToPullback v φ hφ)).op
    (F.obj.map _ g) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  congr 3
  refine congrArg Quiver.Hom.op ?_
  apply MorphismProperty.Over.Hom.ext
  simp [etaleOverHom, homToPullback]

/-- **Pullbacks of sections along isomorphisms over an étale morphism.** If `φ : T ⟶ U` is an
isomorphism over `S` from an étale `V`-scheme to an étale `S`-scheme, then `g ↦ φ^* g` is a
bijection from the sections of `F` over `U` to the sections of `v^* F` over `T`. -/
theorem pullSection_bijective_of_isIso {T : V.Etale} {U : S.Etale} (φ : T.left ⟶ U.left)
    [IsIso φ] (hφ : φ ≫ U.hom = T.hom ≫ v) : Function.Bijective (pullSection v F φ hφ) := by
  let ψ := etaleOverHom v φ hφ
  have : IsIso ψ := by
    refine ⟨MorphismProperty.Over.homMk (inv φ) (by simp [hφ]), ?_, ?_⟩ <;>
      apply MorphismProperty.Over.Hom.ext <;> simp [ψ, etaleOverHom]
  set ι := (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} v hv).app F
  have hι : Function.Bijective (ι.hom.hom.app (op T)) :=
    ((forget AddCommGrpCat.{u + 1}).mapIso
      ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op T)).mapIso ι)).toEquiv.bijective
  have hψ : Function.Bijective (F.obj.map ψ.op) :=
    ((forget AddCommGrpCat.{u + 1}).mapIso (F.obj.mapIso (asIso ψ).op)).toEquiv.bijective
  have key : ι.hom.hom.app (op T) ∘ pullSection v F φ hφ = F.obj.map ψ.op := by
    funext g
    exact upperStarIsoLocalizationRestriction_pullSection v F φ hφ g
  refine ⟨fun g₁ g₂ h ↦ hψ.1 ?_, fun s ↦ ?_⟩
  · simpa [← key] using congrArg (ι.hom.hom.app (op T)) h
  · obtain ⟨g, hg⟩ := hψ.2 (ι.hom.hom.app (op T) s)
    exact ⟨g, hι.1 ((congrFun key g).trans hg)⟩

end Etale

end AlgebraicGeometry.Etale
