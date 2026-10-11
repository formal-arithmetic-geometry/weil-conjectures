/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Pasting lemmas for mates

Two formal pasting statements for the calculus of mates (`CategoryTheory.mateEquiv`), used to
show that the base change Künneth maps of
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Exceptional.BaseChange` are compatible with
composition.

Consider two composable adjunctions `P₂ ⊣ G₂`, `P₁ ⊣ G₁` (think of pullback and pushforward
along `g₂`, `g₁`) and an adjunction `P₁₂ ⊣ G₁₂` with an isomorphism `cP : P₁₂ ≅ P₂ ⋙ P₁`, and
similarly on a second row. The first lemma, `CategoryTheory.mateEquiv_app_of_vComp`, computes
the mate of a square `θ₁₂` which is the vertical pasting of two squares `θ₂`, `θ₁`, up to the
composition isomorphisms; the second one, `CategoryTheory.mateEquiv_inv_app_comp`, does the same
for the mates of the inverses of invertible squares, now with respect to adjunctions `G ⊣ R`.

## Main statements

- `CategoryTheory.mateEquiv_whiskerTop`, `CategoryTheory.mateEquiv_whiskerBottom`.
- `CategoryTheory.mateEquiv_app_of_vComp`.
- `CategoryTheory.mateEquiv_inv_app_comp`.

-/

@[expose] public section

namespace CategoryTheory

open Functor TwoSquare

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

section Whisker

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  {T T' : C₁ ⥤ C₂} {L₁ : C₁ ⥤ C₃} {R₁ : C₃ ⥤ C₁} {L₂ : C₂ ⥤ C₄} {R₂ : C₄ ⥤ C₂}
  {B B' : C₃ ⥤ C₄} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The mate of a square whiskered at the top is the mate whiskered at the right. -/
lemma mateEquiv_whiskerTop (w : TwoSquare T' L₁ L₂ B) (α : T ⟶ T') :
    mateEquiv adj₁ adj₂ (w.whiskerTop α) = (mateEquiv adj₁ adj₂ w).whiskerRight α := by
  ext X
  simp only [mateEquiv_apply, TwoSquare.whiskerTop_app, TwoSquare.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  rw [← Adjunction.unit_naturality_assoc]
  rfl

/-- The mate of a square whiskered at the bottom is the mate whiskered at the left. -/
lemma mateEquiv_whiskerBottom (w : TwoSquare T L₁ L₂ B) (β : B ⟶ B') :
    mateEquiv adj₁ adj₂ (w.whiskerBottom β) = (mateEquiv adj₁ adj₂ w).whiskerLeft β := by
  ext X
  simp only [mateEquiv_apply, TwoSquare.whiskerBottom_app, TwoSquare.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  congr 2
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact (β.naturality _).symm

end Whisker

section Pasting

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {D₁ : Type u₄} {D₂ : Type u₅}
  {D₃ : Type u₆} [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [Category.{v₄} D₁] [Category.{v₅} D₂] [Category.{v₆} D₃]

section LeftAdjoints

variable {P₁ : C₂ ⥤ C₁} {P₂ : C₃ ⥤ C₂} {P₁₂ : C₃ ⥤ C₁} {G₁ : C₁ ⥤ C₂} {G₂ : C₂ ⥤ C₃}
  {G₁₂ : C₁ ⥤ C₃} {Q₁ : D₂ ⥤ D₁} {Q₂ : D₃ ⥤ D₂} {Q₁₂ : D₃ ⥤ D₁} {H₁ : D₁ ⥤ D₂}
  {H₂ : D₂ ⥤ D₃} {H₁₂ : D₁ ⥤ D₃}
  (a₁ : P₁ ⊣ G₁) (a₂ : P₂ ⊣ G₂) (a₁₂ : P₁₂ ⊣ G₁₂) (b₁ : Q₁ ⊣ H₁) (b₂ : Q₂ ⊣ H₂)
  (b₁₂ : Q₁₂ ⊣ H₁₂) (cP : P₁₂ ≅ P₂ ⋙ P₁) (cQ : Q₁₂ ≅ Q₂ ⋙ Q₁)
  {E₁ E₁' : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂} {E₃ : C₃ ⥤ D₃} (κ : E₁ ≅ E₁')
  (θ₁ : TwoSquare E₂ P₁ Q₁ E₁) (θ₂ : TwoSquare E₃ P₂ Q₂ E₂) (θ₁₂ : TwoSquare E₃ P₁₂ Q₁₂ E₁')

/-- **Mates of a pasted square.** If `θ₁₂` is the vertical pasting of `θ₂` and `θ₁`, up to the
composition isomorphisms `cP`, `cQ` and an isomorphism `κ` of the bottom functors, i.e.
`θ₁₂ = cQ ≫ Q₁ θ₂ ≫ θ₁ P₂ ≫ E₁ cP⁻¹ ≫ κ`, then its mate along `a₁₂`, `b₁₂` is the horizontal
pasting of the mates of `θ₂` and `θ₁`, up to the conjugate isomorphisms
`G₁₂ ≅ G₁ ⋙ G₂` and `H₁ ⋙ H₂ ≅ H₁₂`. -/
lemma mateEquiv_app_of_vComp
    (h : ∀ K, θ₁₂.natTrans.app K = cQ.hom.app (E₃.obj K) ≫ Q₁.map (θ₂.natTrans.app K) ≫
      θ₁.natTrans.app (P₂.obj K) ≫ E₁.map (cP.inv.app K) ≫ κ.hom.app (P₁₂.obj K))
    (F : C₁) :
    (mateEquiv a₁₂ b₁₂ θ₁₂).natTrans.app F =
      E₃.map ((conjugateEquiv a₁₂ (a₂.comp a₁) cP.inv).app F) ≫
        (mateEquiv a₂ b₂ θ₂).natTrans.app (G₁.obj F) ≫
        H₂.map ((mateEquiv a₁ b₁ θ₁).natTrans.app F) ≫
        (conjugateEquiv (b₂.comp b₁) b₁₂ cQ.hom).app (E₁.obj F) ≫
        H₁₂.map (κ.hom.app F) := by
  have hθ : θ₁₂ = (((θ₂ ≫ᵥ θ₁).whiskerRight cQ.hom).whiskerLeft cP.inv).whiskerBottom κ.hom := by
    ext K
    rw [h K]
    simp
  rw [hθ, mateEquiv_whiskerBottom, conjugateEquiv_mateEquiv_vcomp _ (a₂.comp a₁),
    mateEquiv_conjugateEquiv_vcomp _ (b₂.comp b₁), mateEquiv_hcomp]
  simp

end LeftAdjoints

section RightAdjoints

variable {G₁ : C₁ ⥤ C₂} {G₂ : C₂ ⥤ C₃} {G₁₂ : C₁ ⥤ C₃} {R₁ : C₂ ⥤ C₁} {R₂ : C₃ ⥤ C₂}
  {R₁₂ : C₃ ⥤ C₁} {H₁ : D₁ ⥤ D₂} {H₂ : D₂ ⥤ D₃} {H₁₂ : D₁ ⥤ D₃} {S₁ : D₂ ⥤ D₁}
  {S₂ : D₃ ⥤ D₂} {S₁₂ : D₃ ⥤ D₁}
  (a₁ : G₁ ⊣ R₁) (a₂ : G₂ ⊣ R₂) (a₁₂ : G₁₂ ⊣ R₁₂) (b₁ : H₁ ⊣ S₁) (b₂ : H₂ ⊣ S₂)
  (b₁₂ : H₁₂ ⊣ S₁₂) (ιG : G₁₂ ⟶ G₁ ⋙ G₂) (ιH : H₁ ⋙ H₂ ⟶ H₁₂) [IsIso ιG] [IsIso ιH]
  {E₁ E₁' : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂} {E₃ : C₃ ⥤ D₃} (κ : E₁ ≅ E₁')
  (K₁ : TwoSquare G₁ E₁ E₂ H₁) (K₂ : TwoSquare G₂ E₂ E₃ H₂) (K₁₂ : TwoSquare G₁₂ E₁' E₃ H₁₂)
  [IsIso K₁.natTrans] [IsIso K₂.natTrans] [IsIso K₁₂.natTrans]

/-- **Composition of the mates of inverses.** Let `K₁`, `K₂`, `K₁₂` be invertible squares with
`K₁₂ = E₃ ιG ≫ K₂ G₁ ≫ H₂ K₁ ≫ ιH E₁ ≫ H₁₂ κ`. Then the mate of `K₁₂⁻¹` along `a₁₂`, `b₁₂` is,
up to the conjugate isomorphisms `R₂ ⋙ R₁ ≅ R₁₂` and `S₁₂ ≅ S₂ ⋙ S₁` and `κ`, the horizontal
pasting of the mates of `K₂⁻¹` and `K₁⁻¹`. -/
lemma mateEquiv_inv_app_comp
    (h : ∀ F, K₁₂.natTrans.app F = E₃.map (ιG.app F) ≫ K₂.natTrans.app (G₁.obj F) ≫
      H₂.map (K₁.natTrans.app F) ≫ ιH.app (E₁.obj F) ≫ H₁₂.map (κ.hom.app F))
    (L : C₃) :
    (mateEquiv a₁ b₁ (inv K₁.natTrans)).natTrans.app (R₂.obj L) ≫
        S₁.map ((mateEquiv a₂ b₂ (inv K₂.natTrans)).natTrans.app L) =
      E₁.map ((conjugateEquiv (a₁.comp a₂) a₁₂ ιG).app L) ≫ κ.hom.app _ ≫
        (mateEquiv a₁₂ b₁₂ (inv K₁₂.natTrans)).natTrans.app L ≫
        (conjugateEquiv b₁₂ (b₁.comp b₂) ιH).app (E₃.obj L) := by
  -- the inverse of `K₁₂` is the vertical pasting of the inverses, up to the isomorphisms
  have hV : ((inv K₁.natTrans : TwoSquare E₁ G₁ H₁ E₂) ≫ᵥ (inv K₂.natTrans : TwoSquare E₂ G₂ H₂ E₃))
      = (((inv K₁₂.natTrans : TwoSquare E₁' G₁₂ H₁₂ E₃).whiskerTop κ.hom).whiskerRight
          ιH).whiskerLeft ιG := by
    ext F
    have hinv : inv (K₁₂.natTrans.app F) = H₁₂.map (κ.inv.app F) ≫ inv (ιH.app (E₁.obj F)) ≫
        H₂.map (inv (K₁.natTrans.app F)) ≫ inv (K₂.natTrans.app (G₁.obj F)) ≫
        E₃.map (inv (ιG.app F)) := by
      rw [h F]
      simp [Functor.map_inv]
    simp only [vComp_app, TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app,
      TwoSquare.whiskerTop_app, Functor.comp_obj, NatIso.isIso_inv_app, hinv]
    simp [← Functor.map_comp_assoc, Functor.map_inv]
  have key := mateEquiv_hcomp a₁ b₁ a₂ b₂ (inv K₁.natTrans) (inv K₂.natTrans)
  rw [hV, conjugateEquiv_mateEquiv_vcomp _ a₁₂, mateEquiv_conjugateEquiv_vcomp _ b₁₂,
    mateEquiv_whiskerTop] at key
  have := congr_app key.symm L
  simp only [hComp_app, TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
    TwoSquare.whiskerRight_app, Functor.comp_obj] at this
  rw [this]
  simp [conjugateEquiv_apply_app]

end RightAdjoints

end Pasting

end CategoryTheory
