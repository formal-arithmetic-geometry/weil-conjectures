/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate

/-! # Changing all four pullback coordinates of an open exchange -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
  {J : A ⥤ B} {P P₀ : B ⥤ A} {J' : A' ⥤ B'} {P' P₀' : B' ⥤ A'}
  {G G₀ : A ⥤ A'} {H H₀ : B ⥤ B'}

private lemma purity_exchangeLeft_eq_inverseMate (a : J ⊣ P) (a' : J' ⊣ P')
    (θ : P ⋙ G ≅ H ⋙ P') :
    exchangeLeft a a' θ = ((mateEquiv a a').symm θ.hom).natTrans := by
  ext K
  simp [exchangeLeft_app, mateEquiv]

/-- Inverse mates respect simultaneous changes of the four pullback functors. -/
theorem purity_exchangeLeft_coordinates (a : J ⊣ P₀) (a' : J' ⊣ P₀')
    (p : P₀ ≅ P) (p' : P₀' ≅ P') (g : G ≅ G₀) (h : H ≅ H₀)
    (θ : P ⋙ G ≅ H ⋙ P') (θ₀ : P₀ ⋙ G₀ ≅ H₀ ⋙ P₀')
    (hθ : θ.hom =
      Functor.whiskerLeft P g.hom ≫ Functor.whiskerRight p.inv G₀ ≫ θ₀.hom ≫
        Functor.whiskerLeft H₀ p'.hom ≫ Functor.whiskerRight h.inv P') :
    exchangeLeft (a.ofNatIsoRight p) (a'.ofNatIsoRight p') θ =
      Functor.whiskerRight g.hom J' ≫ exchangeLeft a a' θ₀ ≫
        Functor.whiskerLeft J h.inv := by
  calc
    exchangeLeft (a.ofNatIsoRight p) (a'.ofNatIsoRight p') θ =
        ((mateEquiv (a.ofNatIsoRight p) (a'.ofNatIsoRight p')).symm θ.hom).natTrans :=
      purity_exchangeLeft_eq_inverseMate (a.ofNatIsoRight p) (a'.ofNatIsoRight p') θ
    _ = Functor.whiskerRight g.hom J' ≫ exchangeLeft a a' θ₀ ≫
        Functor.whiskerLeft J h.inv := by
      rw [purity_exchangeLeft_eq_inverseMate a a' θ₀]
      apply (mateEquiv (a.ofNatIsoRight p) (a'.ofNatIsoRight p')).injective
      rw [Equiv.apply_symm_apply, mateEquiv_comp_whiskerLeft, mateEquiv_whiskerRight_comp,
        mateEquiv_ofNatIsoRight, Equiv.apply_symm_apply]
      ext K
      simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Category.assoc] using congr_app hθ K

end CategoryTheory.Adjunction
