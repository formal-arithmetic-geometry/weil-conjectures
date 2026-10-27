/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate

/-!
# The exchange morphism of an isomorphism is its mate

For adjunctions `af : Lf ⊣ Rf`, `af' : Lf' ⊣ Rf'` and an isomorphism `θ : G ⋙ Lf' ≅ Lf ⋙ G'`,
the exchange morphism `exchangeRight af af' θ : Rf ⋙ G ⟶ G' ⋙ Rf'` is the mate of `θ.hom`
(`CategoryTheory.Adjunction.mateEquiv_eq_exchangeRight`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {B A B' A' : Type*} [Category* B] [Category* A] [Category* B'] [Category* A']

/-- The exchange morphism of `θ` is the mate of `θ.hom`. -/
lemma mateEquiv_eq_exchangeRight {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
    {G : B ⥤ B'} {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θ : G ⋙ Lf' ≅ Lf ⋙ G') :
    mateEquiv af af' θ.hom = exchangeRight af af' θ := by
  ext K
  simp [exchangeRight_app, mateEquiv_apply]

end CategoryTheory.Adjunction
