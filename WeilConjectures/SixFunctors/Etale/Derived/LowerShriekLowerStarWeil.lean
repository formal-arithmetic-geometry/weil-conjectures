/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# `Ra_! ≅ Ra_*` and the Frobenius data

For a proper morphism `a : X ⟶ Y` and a cartesian square `g ≫ a = a ≫ h`, the isomorphism
`Ra_! ≅ Ra_*` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`)
intertwines the Weil data `AlgebraicGeometry.Etale.lowerShriekWeilDatum` and
`AlgebraicGeometry.Etale.lowerStarWeilDatum` as soon as it intertwines the exchange maps
`Ex_! : Lh^* Ra_! ⟶ Ra_! Lg^*` and `Ex_* : Lh^* Ra_* ⟶ Ra_* Lg^*`
(`lowerShriekWeilDatum_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar`).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category* C] [Category* D]

/-- If `σ : Fl ⟶ Fs` intertwines exchange maps `ex₁ : Fl ⋙ Lh ⟶ Lg ⋙ Fl` and
`ex₂ : Fs ⋙ Lh ⟶ Lg ⋙ Fs`, it intertwines the induced structure morphisms `Lh (Fl K) ⟶ Fl K`
and `Lh (Fs K) ⟶ Fs K` of a structure morphism `φ : Lg K ⟶ K`. -/
lemma comp_map_comp_app_of_whisker_eq {Fl Fs : C ⥤ D} {Lg : C ⥤ C} {Lh : D ⥤ D}
    (ex₁ : Fl ⋙ Lh ⟶ Lg ⋙ Fl) (ex₂ : Fs ⋙ Lh ⟶ Lg ⋙ Fs) (σ : Fl ⟶ Fs)
    (hEx : ex₁ ≫ Functor.whiskerLeft Lg σ = Functor.whiskerRight σ Lh ≫ ex₂) {K : C}
    (φ : Lg.obj K ⟶ K) :
    (ex₁.app K ≫ Fl.map φ) ≫ σ.app K = Lh.map (σ.app K) ≫ ex₂.app K ≫ Fs.map φ := by
  have h₁ := NatTrans.congr_app hEx K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h₁
  rw [Category.assoc, σ.naturality φ, reassoc_of% h₁]

end CategoryTheory.NatTrans

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} {a : X ⟶ Y} [IsProper a]
  {g : X ⟶ X} {h : Y ⟶ Y}

/-- The isomorphism `Ra_! ≅ Ra_*` intertwines the exchange maps `Ex_!` and `Ex_*`. -/
def ExchangeCompatible (sq : IsPullback g a a h) : Prop :=
  rightDerivedLowerShriekBaseChangeMap Λ sq ≫
      Functor.whiskerLeft L((g)^*[ModuleCat.{u + 1} Λ])
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) a).hom =
    Functor.whiskerRight (rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} Λ) a).hom L((h)^*[ModuleCat.{u + 1} Λ]) ≫
      derivedBaseChangeMap _ sq.toCommSq

/-- **`Ra_! ≅ Ra_*` intertwines the Weil data**, provided it intertwines the exchange maps:
for a Weil datum `φ : Lg^* K ⟶ K`, the square
```
  Lh^* Ra_! K ──Lh^* (Ra_! ≅ Ra_*)──▶ Lh^* Ra_* K
       │                                  │
  lowerShriekWeilDatum φ          lowerStarWeilDatum φ
       ▼                                  ▼
    Ra_! K ─────────(Ra_! ≅ Ra_*)───────▶ Ra_* K
```
commutes. -/
theorem lowerShriekWeilDatum_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar
    (sq : IsPullback g a a h) (hEx : ExchangeCompatible (Λ := Λ) sq)
    {K : DerivedCategoryModule Λ X} (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    lowerShriekWeilDatum sq φ ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) a).hom.app K =
      (L((h)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) a).hom.app K) ≫
        lowerStarWeilDatum sq.toCommSq φ := by
  exact CategoryTheory.NatTrans.comp_map_comp_app_of_whisker_eq _ _ _ hEx φ

end Etale

end AlgebraicGeometry
