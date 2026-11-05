/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.ProjectionPushNormalization

/-! # Components of a transported push comparison from a normalized mate

If the mate of a square `α` is normalized as `aD ≫ d₁ ≫ d₂ ≫ R'.map aC.inv` (the shape of
`nativeProjectionPushMate_normalization`), the push comparison transported along `aC`, `aD`
has components `d₁ ≫ d₂`. The hypothesis is stated in exactly that four-factor shape so that
it is instantiated by the concrete normalization lemma without rewriting. -/

@[expose] public section

namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {G : A ⥤ C} {H : B ⥤ D} {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}

/-- The components of the transported push comparison of a mate, from a normalization of the
mate in four factors. -/
lemma projectionPushForgetIso_mateEquiv_hom_app (a : L ⊣ R) (b : L' ⊣ R')
    (α : TwoSquare G L L' H) [IsIso (mateEquiv a b α).natTrans]
    {FC : B ⥤ D} {FD : A ⥤ C} (aC : H ≅ FC) (aD : G ≅ FD) (M : B) {Z : C}
    (d₁ : FD.obj (R.obj M) ⟶ Z) (d₂ : Z ⟶ R'.obj (FC.obj M))
    (h : (mateEquiv a b α).app M =
      aD.hom.app (R.obj M) ≫ d₁ ≫ d₂ ≫ R'.map (aC.inv.app M)) :
    (projectionPushForgetIso (asIso (mateEquiv a b α).natTrans) aC aD).hom.app M =
      d₁ ≫ d₂ :=
  projectionPushForgetIso_hom_app_of_factorization (asIso (mateEquiv a b α).natTrans) aC aD M
    (d₁ ≫ d₂) (by rw [asIso_hom, Category.assoc]; exact h)

end CategoryTheory
