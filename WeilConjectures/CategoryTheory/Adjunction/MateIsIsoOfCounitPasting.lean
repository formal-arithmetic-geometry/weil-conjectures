/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Invertibility of a mate through a factorization of the horizontal functors

Consider adjunctions `T_W ⊣ R_W`, `T_A ⊣ R_A`, `T_B ⊣ R_B` and horizontal functors
`F_Z ≅ U_Z ⋙ Φ_Z`, `F_Y ≅ U_Y ⋙ Φ_Y` forming two invertible squares
`σ : T_W ⋙ U_Y ≅ U_Z ⋙ T_A` and `ρ : T_A ⋙ Φ_Y ≅ Φ_Z ⋙ T_B`:
```
        U_Z        Φ_Z
  W_Z -----> A_Z -----> B_Z
   |          |          |
  T_W   σ    T_A   ρ    T_B
   v          v          v
  W_Y -----> A_Y -----> B_Y
        U_Y        Φ_Y
```
Suppose that the counit of `T_W ⊣ R_W` lies over the counit of `T_A ⊣ R_A` up to `σ` and an
isomorphism `U_Z (R_W L) ≅ R_A (U_Y L)`, and that the mate of `ρ⁻¹` is invertible (e.g. because
`Φ_Z`, `Φ_Y` are equivalences). Then the mate `F_Z ∘ R_W ⟶ R_B ∘ F_Y` of the pasted square
`β : F_Z ⋙ T_B ⟶ T_W ⋙ F_Y` is invertible
(`CategoryTheory.isIso_mateEquiv_app_of_counit_of_pasting`).

The mate of `σ` itself need not be invertible in the situations where this is applied: `U_Z` is
not full, and the argument only uses that the counit of `R_W` lies over that of `R_A`.
-/

@[expose] public section

namespace CategoryTheory

variable {W_Z W_Y A_Z A_Y B_Z B_Y : Type*} [Category* W_Z] [Category* W_Y] [Category* A_Z]
  [Category* A_Y] [Category* B_Z] [Category* B_Y]
  {T_W : W_Z ⥤ W_Y} {R_W : W_Y ⥤ W_Z} {T_A : A_Z ⥤ A_Y} {R_A : A_Y ⥤ A_Z}
  {T_B : B_Z ⥤ B_Y} {R_B : B_Y ⥤ B_Z}
  {U_Z : W_Z ⥤ A_Z} {U_Y : W_Y ⥤ A_Y} {Φ_Z : A_Z ⥤ B_Z} {Φ_Y : A_Y ⥤ B_Y}
  {F_Z : W_Z ⥤ B_Z} {F_Y : W_Y ⥤ B_Y}

/-- The component of the mate of the pasted square `β`, written through the mate of `ρ⁻¹` and
the isomorphism `U_Z (R_W L) ≅ R_A (U_Y L)` under which the counits correspond. -/
lemma mateEquiv_app_eq_of_counit_of_pasting (adjW : T_W ⊣ R_W) (adjA : T_A ⊣ R_A)
    (adjB : T_B ⊣ R_B) (σ : T_W ⋙ U_Y ≅ U_Z ⋙ T_A) (ρ : T_A ⋙ Φ_Y ≅ Φ_Z ⋙ T_B)
    (eZ : F_Z ≅ U_Z ⋙ Φ_Z) (eY : F_Y ≅ U_Y ⋙ Φ_Y) (β : F_Z ⋙ T_B ⟶ T_W ⋙ F_Y)
    (hβ : ∀ M, β.app M = T_B.map (eZ.hom.app M) ≫ ρ.inv.app (U_Z.obj M) ≫
      Φ_Y.map (σ.inv.app M) ≫ eY.inv.app (T_W.obj M))
    (L : W_Y) (e : U_Z.obj (R_W.obj L) ≅ R_A.obj (U_Y.obj L))
    (he : U_Y.map (adjW.counit.app L) =
      σ.hom.app (R_W.obj L) ≫ T_A.map e.hom ≫ adjA.counit.app (U_Y.obj L)) :
    (mateEquiv adjW adjB (TwoSquare.mk _ _ _ _ β)).app L =
      eZ.hom.app (R_W.obj L) ≫ Φ_Z.map e.hom ≫
        (mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ ρ.inv)).app (U_Y.obj L) ≫
          R_B.map (eY.inv.app L) := by
  apply (adjB.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, mateEquiv_counit, hβ]
  simp only [Functor.map_comp, Category.assoc, Adjunction.counit_naturality]
  erw [reassoc_of% (mateEquiv_counit adjA adjB (TwoSquare.mk _ _ _ _ ρ.inv) (U_Y.obj L))]
  have hY := eY.inv.naturality (adjW.counit.app L)
  have hρ := ρ.inv.naturality e.hom
  dsimp at hY hρ ⊢
  rw [← hY, he, ← Φ_Y.map_comp_assoc, Iso.inv_hom_id_app_assoc, Φ_Y.map_comp, Category.assoc,
    ← reassoc_of% hρ]

/-- **Invertibility of a mate through a factorization of the horizontal functors.** If the
counit of `T_W ⊣ R_W` lies over that of `T_A ⊣ R_A` and the mate of `ρ⁻¹` is invertible, then
the mate `F_Z ∘ R_W ⟶ R_B ∘ F_Y` of the pasted square `β` is invertible. -/
lemma isIso_mateEquiv_app_of_counit_of_pasting (adjW : T_W ⊣ R_W) (adjA : T_A ⊣ R_A)
    (adjB : T_B ⊣ R_B) (σ : T_W ⋙ U_Y ≅ U_Z ⋙ T_A) (ρ : T_A ⋙ Φ_Y ≅ Φ_Z ⋙ T_B)
    (eZ : F_Z ≅ U_Z ⋙ Φ_Z) (eY : F_Y ≅ U_Y ⋙ Φ_Y) (β : F_Z ⋙ T_B ⟶ T_W ⋙ F_Y)
    (hβ : ∀ M, β.app M = T_B.map (eZ.hom.app M) ≫ ρ.inv.app (U_Z.obj M) ≫
      Φ_Y.map (σ.inv.app M) ≫ eY.inv.app (T_W.obj M))
    (hcounit : ∀ L, ∃ e : U_Z.obj (R_W.obj L) ≅ R_A.obj (U_Y.obj L),
      U_Y.map (adjW.counit.app L) =
        σ.hom.app (R_W.obj L) ≫ T_A.map e.hom ≫ adjA.counit.app (U_Y.obj L))
    (hρ : ∀ Y, IsIso ((mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ ρ.inv)).app Y)) (L : W_Y) :
    IsIso ((mateEquiv adjW adjB (TwoSquare.mk _ _ _ _ β)).app L) := by
  obtain ⟨e, he⟩ := hcounit L
  rw [mateEquiv_app_eq_of_counit_of_pasting adjW adjA adjB σ ρ eZ eY β hβ L e he]
  have := hρ (U_Y.obj L)
  infer_instance

/-- The variant of `CategoryTheory.isIso_mateEquiv_app_of_counit_of_pasting` for an invertible
pasted square `β`, described through its inverse. -/
lemma isIso_mateEquiv_app_of_counit_of_pasting_inv (adjW : T_W ⊣ R_W) (adjA : T_A ⊣ R_A)
    (adjB : T_B ⊣ R_B) (σ : T_W ⋙ U_Y ≅ U_Z ⋙ T_A) (ρ : T_A ⋙ Φ_Y ≅ Φ_Z ⋙ T_B)
    (eZ : F_Z ≅ U_Z ⋙ Φ_Z) (eY : F_Y ≅ U_Y ⋙ Φ_Y) (β : F_Z ⋙ T_B ≅ T_W ⋙ F_Y)
    (hβ : ∀ M, β.inv.app M = eY.hom.app (T_W.obj M) ≫ Φ_Y.map (σ.hom.app M) ≫
      ρ.hom.app (U_Z.obj M) ≫ T_B.map (eZ.inv.app M))
    (hcounit : ∀ L, ∃ e : U_Z.obj (R_W.obj L) ≅ R_A.obj (U_Y.obj L),
      U_Y.map (adjW.counit.app L) =
        σ.hom.app (R_W.obj L) ≫ T_A.map e.hom ≫ adjA.counit.app (U_Y.obj L))
    (hρ : ∀ Y, IsIso ((mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ ρ.inv)).app Y)) (L : W_Y) :
    IsIso ((mateEquiv adjW adjB (TwoSquare.mk _ _ _ _ β.hom)).app L) := by
  refine isIso_mateEquiv_app_of_counit_of_pasting adjW adjA adjB σ ρ eZ eY β.hom
    (fun M ↦ ?_) hcounit hρ L
  rw [← cancel_mono (β.inv.app M), Iso.hom_inv_id_app, hβ]
  simp [← Functor.map_comp, ← Functor.map_comp_assoc]

end CategoryTheory
