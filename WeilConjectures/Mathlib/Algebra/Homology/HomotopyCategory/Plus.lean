/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Natural transformations between functors on bounded below homotopy categories

A natural transformation `τ : F ⟶ G` of additive functors induces a natural transformation
`F.mapHomotopyCategoryPlus ⟶ G.mapHomotopyCategoryPlus` between the induced functors on the
bounded below homotopy categories (`CategoryTheory.NatTrans.mapHomotopyCategoryPlus`),
compatibly with identities and compositions.

Moreover, the functor `(𝟭 C).mapHomotopyCategoryPlus` induced by the identity functor is
isomorphic to the identity functor (`CategoryTheory.Functor.mapHomotopyCategoryPlusIdIso`).
Both this isomorphism and Mathlib's `CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso`
attached to `Iso.refl (F ⋙ G)` are in fact identities
(`CategoryTheory.Functor.mapHomotopyCategoryPlusIdIso_hom_app_eq_id` and
`CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app`), together with their
inverse forms. Both are computed from their unbounded counterparts through the fully
faithful inclusion `HomotopyCategory.Plus.ι`
(`CategoryTheory.Functor.ι_map_mapHomotopyCategoryPlusIdIso_hom_app` and
`CategoryTheory.Functor.ι_map_mapHomotopyCategoryPlusCompIso_hom_app`).

This material is destined for `Mathlib/Algebra/Homology/HomotopyCategory/Plus.lean`, next to
`CategoryTheory.Functor.mapHomotopyCategoryPlus`.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

namespace CategoryTheory.NatTrans

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]

/-- The natural transformation `F.mapHomotopyCategoryPlus ⟶ G.mapHomotopyCategoryPlus`
induced by a natural transformation `τ : F ⟶ G` of additive functors. It is the
transformation `NatTrans.mapHomotopyCategory τ` of the ambient homotopy categories,
lifted through the fully faithful inclusion of the bounded below subcategory. -/
noncomputable def mapHomotopyCategoryPlus
    {F G : C ⥤ D} [F.Additive] [G.Additive] (τ : F ⟶ G) :
    F.mapHomotopyCategoryPlus ⟶ G.mapHomotopyCategoryPlus :=
  ((HomotopyCategory.plus D).fullyFaithfulι.whiskeringRight (HomotopyCategory.Plus C)).preimage
    (Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
      (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)))

@[simp]
lemma mapHomotopyCategoryPlus_id (F : C ⥤ D) [F.Additive] :
    NatTrans.mapHomotopyCategoryPlus (𝟙 F) = 𝟙 F.mapHomotopyCategoryPlus := by
  rw [NatTrans.mapHomotopyCategoryPlus, NatTrans.mapHomotopyCategory_id (ComplexShape.up ℤ),
    Functor.whiskerLeft_id']
  exact ((HomotopyCategory.plus D).fullyFaithfulι.whiskeringRight
    (HomotopyCategory.Plus C)).preimage_id

@[reassoc, simp]
lemma mapHomotopyCategoryPlus_comp {F G H : C ⥤ D}
    [F.Additive] [G.Additive] [H.Additive] (τ : F ⟶ G) (σ : G ⟶ H) :
    NatTrans.mapHomotopyCategoryPlus (τ ≫ σ) =
      NatTrans.mapHomotopyCategoryPlus τ ≫ NatTrans.mapHomotopyCategoryPlus σ := by
  have h : Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
        (NatTrans.mapHomotopyCategory (τ ≫ σ) (ComplexShape.up ℤ)) =
      Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
          (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)) ≫
        Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
          (NatTrans.mapHomotopyCategory σ (ComplexShape.up ℤ)) := by
    rw [NatTrans.mapHomotopyCategory_comp (ComplexShape.up ℤ)]
    rfl
  rw [NatTrans.mapHomotopyCategoryPlus, NatTrans.mapHomotopyCategoryPlus,
    NatTrans.mapHomotopyCategoryPlus, h]
  exact ((HomotopyCategory.plus D).fullyFaithfulι.whiskeringRight
    (HomotopyCategory.Plus C)).preimage_comp (Y := G.mapHomotopyCategoryPlus) _ _

end CategoryTheory.NatTrans

namespace CategoryTheory.Functor

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]

/-- The functor on bounded below homotopy categories induced by the identity functor is
isomorphic to the identity functor: the bounded below counterpart of
`CategoryTheory.Functor.mapHomotopyCategoryIdIso`. -/
noncomputable def mapHomotopyCategoryPlusIdIso :
    (𝟭 C).mapHomotopyCategoryPlus ≅ 𝟭 (HomotopyCategory.Plus C) :=
  fullyFaithfulCancelRight (HomotopyCategory.Plus.ι C)
    (isoWhiskerLeft (HomotopyCategory.Plus.ι C)
        (mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)) ≪≫
      (HomotopyCategory.Plus.ι C).rightUnitor ≪≫
      (HomotopyCategory.Plus.ι C).leftUnitor.symm)

@[simp]
lemma ι_map_mapHomotopyCategoryPlusIdIso_hom_app (K : HomotopyCategory.Plus C) :
    (HomotopyCategory.Plus.ι C).map ((mapHomotopyCategoryPlusIdIso C).hom.app K) =
      (mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom.app K.obj := by
  rw [mapHomotopyCategoryPlusIdIso, fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  simp

@[simp]
lemma ι_map_mapHomotopyCategoryPlusIdIso_inv_app (K : HomotopyCategory.Plus C) :
    (HomotopyCategory.Plus.ι C).map ((mapHomotopyCategoryPlusIdIso C).inv.app K) =
      (mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).inv.app K.obj := by
  rw [mapHomotopyCategoryPlusIdIso, fullyFaithfulCancelRight_inv_app,
    Functor.map_preimage]
  simp

/-- The isomorphism `Functor.mapHomotopyCategoryPlusIdIso` is the identity: this is the
bounded below counterpart of `Functor.mapHomotopyCategoryIdIso_hom_app_eq_id`. -/
@[simp]
lemma mapHomotopyCategoryPlusIdIso_hom_app_eq_id (K : HomotopyCategory.Plus C) :
    (mapHomotopyCategoryPlusIdIso C).hom.app K = 𝟙 K := by
  apply (HomotopyCategory.Plus.ι C).map_injective
  -- `rw` cannot rewrite under the identity here, so produce the identity on the right first
  refine Eq.trans ?_ ((HomotopyCategory.Plus.ι C).map_id K).symm
  rw [ι_map_mapHomotopyCategoryPlusIdIso_hom_app]
  exact mapHomotopyCategoryIdIso_hom_app_eq_id C (ComplexShape.up ℤ) K.obj

/-- The inverse of `Functor.mapHomotopyCategoryPlusIdIso` is the identity. -/
@[simp]
lemma mapHomotopyCategoryPlusIdIso_inv_app_eq_id (K : HomotopyCategory.Plus C) :
    (mapHomotopyCategoryPlusIdIso C).inv.app K = 𝟙 K :=
  congrArg Iso.inv (Iso.ext (mapHomotopyCategoryPlusIdIso_hom_app_eq_id C K) :
    (mapHomotopyCategoryPlusIdIso C).app K = Iso.refl _)

section Comp

variable {C}
variable {D : Type u₂} {E : Type u₃} [Category.{v₂} D] [Category.{v₃} E]
  [Preadditive D] [Preadditive E]

/-- The isomorphism `Functor.mapHomotopyCategoryPlusCompIso` is the restriction of
`Functor.mapHomotopyCategoryCompIso` along the fully faithful inclusion
`HomotopyCategory.Plus.ι`. -/
@[simp]
lemma ι_map_mapHomotopyCategoryPlusCompIso_hom_app {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) (K : HomotopyCategory.Plus C) :
    (HomotopyCategory.Plus.ι E).map ((mapHomotopyCategoryPlusCompIso e).hom.app K) =
      (mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app K.obj :=
  rfl

/-- The isomorphism `Functor.mapHomotopyCategoryPlusCompIso` attached to `Iso.refl (F ⋙ G)`
is the identity: this is the bounded below counterpart of
`Functor.mapHomotopyCategoryCompIso_refl_hom_app`. -/
@[simp]
lemma mapHomotopyCategoryPlusCompIso_refl_hom_app (F : C ⥤ D) (G : D ⥤ E) [F.Additive]
    [G.Additive] (K : HomotopyCategory.Plus C) :
    (mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K =
      𝟙 ((F ⋙ G).mapHomotopyCategoryPlus.obj K) := by
  apply (HomotopyCategory.Plus.ι E).map_injective
  -- `rw` cannot rewrite under the identity here, so produce the identity on the right first
  refine Eq.trans ?_ ((HomotopyCategory.Plus.ι E).map_id _).symm
  rw [ι_map_mapHomotopyCategoryPlusCompIso_hom_app]
  exact mapHomotopyCategoryCompIso_refl_hom_app (ComplexShape.up ℤ) F G K.obj

/-- The inverse of `Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))` is the
identity. -/
@[simp]
lemma mapHomotopyCategoryPlusCompIso_refl_inv_app (F : C ⥤ D) (G : D ⥤ E) [F.Additive]
    [G.Additive] (K : HomotopyCategory.Plus C) :
    (mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app K =
      𝟙 ((F ⋙ G).mapHomotopyCategoryPlus.obj K) :=
  congrArg Iso.inv (Iso.ext (mapHomotopyCategoryPlusCompIso_refl_hom_app F G K) :
    (mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).app K = Iso.refl _)

end Comp

end CategoryTheory.Functor
