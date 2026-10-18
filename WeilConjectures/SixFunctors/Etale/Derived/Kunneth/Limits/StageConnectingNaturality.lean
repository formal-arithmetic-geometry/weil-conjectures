/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.StageConnecting

/-!
# Naturality of the connecting maps of the stages of a limit system

The transition maps of a limit system commute with the connecting maps of the long exact
sequences of the stages (`AlgebraicGeometry.Etale.LimitStage.connecting_naturality`), since they
commute with the shifts. This is kept in its own file because its elaboration is memory hungry.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

/-- The connecting maps of the homology sequences of the images of a triangle under two functors
to `D⁺(D)` commute with the maps induced by a natural transformation compatible with the shifts,
with the homology functors written as `H^n` (rather than as shifts of `H^0`). -/
lemma DerivedCategory.Plus.homologySequenceδ_mapTriangle_naturality {C D : Type*} [Category C]
    [Category D] [Abelian D] [HasDerivedCategory D] [HasShift C ℤ]
    {F₁ F₂ : C ⥤ DerivedCategory.Plus D}
    [F₁.CommShift ℤ] [F₂.CommShift ℤ] (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] (T : Triangle C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (DerivedCategory.Plus.homologyFunctor D 0).homologySequenceδ (F₁.mapTriangle.obj T) n₀ n₁ h ≫
        (DerivedCategory.Plus.homologyFunctor D n₁).map (τ.app T.obj₁) =
      (DerivedCategory.Plus.homologyFunctor D n₀).map (τ.app T.obj₃) ≫
        (DerivedCategory.Plus.homologyFunctor D 0).homologySequenceδ (F₂.mapTriangle.obj T) n₀ n₁
          h :=
  (DerivedCategory.Plus.homologyFunctor D 0).homologySequenceδ_mapTriangle_naturality τ T n₀ n₁ h

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

namespace LimitStage

variable {B W : Scheme.{u}}

section LES

variable {E : ShortComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
  (δ : (DerivedCategory.Plus.singleFunctor _ 0).obj E.X₃ ⟶
    ((DerivedCategory.Plus.singleFunctor _ 0).obj E.X₁)⟦(1 : ℤ)⟧)

set_option maxHeartbeats 400000 in
-- the derived-category computation unfolds large terms
/-- The transition maps commute with the connecting maps. -/
lemma connecting_naturality {α β : LimitStage B W} (φ : Hom α β) (n₀ n₁ : ℤ)
    (h : n₀ + 1 = n₁) :
    connecting Λ δ β n₀ n₁ h ≫ (DerivedCategory.Plus.homologyFunctor _ n₁).map
        ((transition Λ φ).app ((DerivedCategory.Plus.singleFunctor _ 0).obj E.X₁)) =
      (DerivedCategory.Plus.homologyFunctor _ n₀).map
        ((transition Λ φ).app ((DerivedCategory.Plus.singleFunctor _ 0).obj E.X₃)) ≫
        connecting Λ δ α n₀ n₁ h :=
  by
  have : NatTrans.CommShift (transition Λ φ) ℤ := inferInstance
  unfold connecting
  exact DerivedCategory.Plus.homologySequenceδ_mapTriangle_naturality (transition Λ φ)
    (Triangle.mk ((DerivedCategory.Plus.singleFunctor _ 0).map E.f)
      ((DerivedCategory.Plus.singleFunctor _ 0).map E.g) δ) n₀ n₁ h

end LES

end LimitStage

end AlgebraicGeometry.Etale
