/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The mates correspondence, in terms of natural transformations

`Mathlib.CategoryTheory.Adjunction.Mates` phrases the pasting laws for the mates
correspondence in terms of the horizontal and vertical composition of
`CategoryTheory.TwoSquare`s. This file restates them as plain equalities of natural
transformations, which is the form in which the exchange transformation of
`WeilConjectures.SixFunctors.UpperLowerStar.BaseChange` uses them, and adds the two
whiskering laws for the *vertical* sides of a square, which have no analogue in Mathlib:
there the mate is whiskered by the very same transformation, since no adjunction is
transported.

## Main results

- `CategoryTheory.mateEquiv_whiskerRight_comp` and
  `CategoryTheory.mateEquiv_comp_whiskerLeft`: whiskering the vertical sides of a square.
- `CategoryTheory.mateEquiv_id`: the mate of the identity square is the identity square.
- `CategoryTheory.mateEquiv_vcomp'` and `CategoryTheory.mateEquiv_hcomp'`: the pasting laws.
-/

@[expose] public section

set_option maxRecDepth 4000

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

open Category Functor Adjunction

section Whisker

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
variable {G G' : C ⥤ E} {H H' : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- Whiskering the top side of a square whiskers its mate on the right by the same
transformation. -/
theorem mateEquiv_whiskerRight_comp (α : G' ⋙ L₂ ⟶ L₁ ⋙ H) (c : G ⟶ G') :
    (mateEquiv adj₁ adj₂ (.mk G L₁ L₂ H (Functor.whiskerRight c L₂ ≫ α))).natTrans =
      Functor.whiskerLeft R₁ c ≫ (mateEquiv adj₁ adj₂ (.mk G' L₁ L₂ H α)).natTrans := by
  ext b
  simp [mateEquiv]

/-- Whiskering the bottom side of a square whiskers its mate on the left by the same
transformation. -/
theorem mateEquiv_comp_whiskerLeft (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (d : H ⟶ H') :
    (mateEquiv adj₁ adj₂ (.mk G L₁ L₂ H' (α ≫ Functor.whiskerLeft L₁ d))).natTrans =
      (mateEquiv adj₁ adj₂ (.mk G L₁ L₂ H α)).natTrans ≫ Functor.whiskerRight d R₂ := by
  ext b
  simp only [mateEquiv, Equiv.coe_fn_mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_obj, Functor.id_obj, Functor.rightUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_id,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp, Category.assoc,
    Functor.comp_map, ← R₂.map_comp, d.naturality]

end Whisker

section Id

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C}

/-- The mate of the identity square on a left adjoint is the identity square on the right
adjoint. -/
theorem mateEquiv_id (adj : L ⊣ R) :
    (mateEquiv adj adj (.mk (𝟭 C) L L (𝟭 D)
        ((Functor.leftUnitor L).hom ≫ (Functor.rightUnitor L).inv))).natTrans =
      (Functor.rightUnitor R).hom ≫ (Functor.leftUnitor R).inv := by
  ext b
  simp [mateEquiv]

end Id

section VComp

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄} {E : Type u₅} {F : Type u₆}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Category.{v₄} D] [Category.{v₅} E] [Category.{v₆} F]
variable {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} {L₃ : E ⥤ F} {R₃ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)

/-- The mates correspondence commutes with pasting two squares along a common horizontal
edge. This is `CategoryTheory.mateEquiv_vcomp`, written out in terms of natural
transformations. -/
theorem mateEquiv_vcomp' (α : G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁) (β : G₂ ⋙ L₃ ⟶ L₂ ⋙ H₂) :
    (mateEquiv adj₁ adj₃ (.mk (G₁ ⋙ G₂) L₁ L₃ (H₁ ⋙ H₂)
        (Functor.whiskerLeft G₁ β ≫ Functor.whiskerRight α H₂))).natTrans =
      Functor.whiskerRight (mateEquiv adj₁ adj₂ (.mk G₁ L₁ L₂ H₁ α)).natTrans G₂ ≫
        Functor.whiskerLeft H₁ (mateEquiv adj₂ adj₃ (.mk G₂ L₂ L₃ H₂ β)).natTrans := by
  have := mateEquiv_vcomp adj₁ adj₂ adj₃ (.mk G₁ L₁ L₂ H₁ α) (.mk G₂ L₂ L₃ H₂ β)
  ext b
  have := congr_app this b
  simpa [TwoSquare.hComp, TwoSquare.vComp] using this

end VComp

section HComp

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄} {E : Type u₅} {F : Type u₆}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Category.{v₄} D] [Category.{v₅} E] [Category.{v₆} F]
variable {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
variable {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)

/-- The mates correspondence commutes with pasting two squares along a common vertical
edge. This is `CategoryTheory.mateEquiv_hcomp`, written out in terms of natural
transformations. -/
theorem mateEquiv_hcomp' (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (β : H ⋙ L₄ ⟶ L₃ ⋙ K) :
    (mateEquiv (adj₁.comp adj₃) (adj₂.comp adj₄) (.mk G (L₁ ⋙ L₃) (L₂ ⋙ L₄) K
        (Functor.whiskerRight α L₄ ≫ Functor.whiskerLeft L₁ β))).natTrans =
      Functor.whiskerLeft R₃ (mateEquiv adj₁ adj₂ (.mk G L₁ L₂ H α)).natTrans ≫
        Functor.whiskerRight (mateEquiv adj₃ adj₄ (.mk H L₃ L₄ K β)).natTrans R₂ := by
  have := mateEquiv_hcomp adj₁ adj₂ adj₃ adj₄ (.mk G L₁ L₂ H α) (.mk H L₃ L₄ K β)
  ext b
  have := congr_app this b
  simpa [TwoSquare.hComp, TwoSquare.vComp] using this

end HComp

section Unitor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C}

/-- The inverse form of `CategoryTheory.conjugateEquiv_leftUnitor_hom`. -/
lemma conjugateEquiv_leftUnitor_inv (adj : L ⊣ R) :
    conjugateEquiv (Adjunction.id.comp adj) adj (Functor.leftUnitor L).inv =
      (Functor.rightUnitor R).hom := by
  cat_disch

/-- The inverse form of `CategoryTheory.conjugateEquiv_rightUnitor_hom`. -/
lemma conjugateEquiv_rightUnitor_inv (adj : L ⊣ R) :
    conjugateEquiv (adj.comp Adjunction.id) adj (Functor.rightUnitor L).inv =
      (Functor.leftUnitor R).hom := by
  cat_disch

end Unitor

section WhiskerAdjoint

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
variable {G : A ⥤ C} {H : B ⥤ D}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} {L₃ : C ⥤ D} {R₃ : D ⥤ C}

/-- Whiskering the right side of a square whiskers its mate on the left by the conjugate
transformation. This is `CategoryTheory.mateEquiv_conjugateEquiv_vcomp`, written out in terms
of natural transformations. -/
theorem mateEquiv_whiskerLeft_comp (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (β : L₃ ⟶ L₂) :
    (mateEquiv adj₁ adj₃ (.mk G L₁ L₃ H (Functor.whiskerLeft G β ≫ α))).natTrans =
      (mateEquiv adj₁ adj₂ (.mk G L₁ L₂ H α)).natTrans ≫
        Functor.whiskerLeft H (conjugateEquiv adj₂ adj₃ β) := by
  have := mateEquiv_conjugateEquiv_vcomp adj₁ adj₂ adj₃ (.mk G L₁ L₂ H α) β
  ext b
  simpa [TwoSquare.whiskerRight, TwoSquare.whiskerBottom] using congr_app this b

end WhiskerAdjoint

section WhiskerAdjoint'

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
variable {G : A ⥤ C} {H : B ⥤ D}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : A ⥤ B} {R₂ : B ⥤ A} {L₃ : C ⥤ D} {R₃ : D ⥤ C}

/-- Whiskering the left side of a square whiskers its mate on the right by the conjugate
transformation. This is `CategoryTheory.conjugateEquiv_mateEquiv_vcomp`, written out in terms
of natural transformations. -/
theorem mateEquiv_comp_whiskerRight (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (α : G ⋙ L₃ ⟶ L₂ ⋙ H) (β : L₂ ⟶ L₁) :
    (mateEquiv adj₁ adj₃ (.mk G L₁ L₃ H (α ≫ Functor.whiskerRight β H))).natTrans =
      Functor.whiskerRight (conjugateEquiv adj₁ adj₂ β) G ≫
        (mateEquiv adj₂ adj₃ (.mk G L₂ L₃ H α)).natTrans := by
  have := conjugateEquiv_mateEquiv_vcomp adj₁ adj₂ adj₃ β (.mk G L₂ L₃ H α)
  ext b
  simpa [TwoSquare.whiskerLeft, TwoSquare.whiskerTop] using congr_app this b

end WhiskerAdjoint'

end CategoryTheory
