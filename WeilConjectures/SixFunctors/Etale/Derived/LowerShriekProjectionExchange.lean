/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# The projection map commutes with the exchange map `Ex_!`

For torsion coefficients, the projection map `PF : Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)`
(`AlgebraicGeometry.Etale.projectionMap`) does not depend on the compactification: the
comparison isomorphisms `Rf_!(c) ≅ Rf_!(d)` intertwine the projection maps
(`AlgebraicGeometry.Etale.projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso`).
Consequently the projection map commutes with the compactly supported base change map
`Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`)
and the tensor comparisons of the derived pullbacks
(`AlgebraicGeometry.Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Independence

variable {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]

/-- The comparison isomorphisms `Rf_!(c) ≅ Rf_!(d)` intertwine the projection maps. -/
lemma projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso
    (c d : Compactification f) (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((projectionMapOfCompactification _ c).app K).app L ≫
        (rightDerivedLowerShriekOfCompactificationIso Λ c d).hom.app
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) =
      ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).map
          ((rightDerivedLowerShriekOfCompactificationIso Λ c d).hom.app K)).app L ≫
        ((projectionMapOfCompactification _ d).app K).app L := by
  trace_state
  sorry

end Independence

section Exchange

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

/-- **The projection map commutes with the exchange map `Ex_!`**: for a cartesian square
`g' ≫ f = f' ≫ g`, the square
```
Lg^*(Rf_!K ⊗ᴸ L) ──Lg^* PF──▶ Lg^*Rf_!(K ⊗ᴸ Lf^*L) ──Ex_!──▶ Rf'_!Lg'^*(K ⊗ᴸ Lf^*L)
       │                                                          │
       ▼                                                          ▼
Lg^*Rf_!K ⊗ᴸ Lg^*L ──Ex_! ⊗ 1──▶ Rf'_!Lg'^*K ⊗ᴸ Lg^*L ──PF──▶ Rf'_!(Lg'^*K ⊗ᴸ Lf'^*Lg^*L)
```
commutes, where the vertical arrows are the tensor comparisons of the derived pullbacks, the
right one followed by `Lg'^*Lf^* ≅ Lf'^*Lg^*`. -/
theorem projectionMap_rightDerivedLowerShriekBaseChangeMap (sq : IsPullback g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    L((g)^*[ModuleCat.{u + 1} Λ]).map (((projectionMap _ f).app K).app L) ≫
        (rightDerivedLowerShriekBaseChangeMap Λ sq).app
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) ≫
        (R(f')_![ModuleCat.{u + 1} Λ]).map
          (((leftDerivedUpperStarTensorComparison _ g').app K).app
            (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) ≫
        (R(f')_![ModuleCat.{u + 1} Λ]).map
          (((-⊗ᴸ-(X')[ModuleCat.{u + 1} Λ]).obj (L((g')^*[ModuleCat.{u + 1} Λ]).obj K)).map
            ((derivedSquareUpperStarIso _ sq.toCommSq).inv.app L)) =
      ((leftDerivedUpperStarTensorComparison _ g).app
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).app L ≫
        ((-⊗ᴸ-(Y')[ModuleCat.{u + 1} Λ]).map
          ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K)).app
            (L((g)^*[ModuleCat.{u + 1} Λ]).obj L) ≫
        ((projectionMap _ f').app (L((g')^*[ModuleCat.{u + 1} Λ]).obj K)).app
          (L((g)^*[ModuleCat.{u + 1} Λ]).obj L) := by
  have thm := projectionMapOfCompactification_baseChange' (ModuleCat.{u + 1} Λ) sq.toCommSq
    (HasCompactification.compactification f)
    ((HasCompactification.compactification f).ofIsPullback sq)
    (pullback.fst (HasCompactification.compactification f).g g)
    ((HasCompactification.compactification f).isPullback_i_ofIsPullback sq)
    (IsPullback.of_hasPullback (HasCompactification.compactification f).g g).toCommSq K L
  rw [← rightDerivedLowerShriekOfCompactificationBaseChangeMap_eq] at thm
  have hD := projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso Λ
    ((HasCompactification.compactification f).ofIsPullback sq) (HasCompactification.compactification f')
    (L((g')^*[ModuleCat.{u + 1} Λ]).obj K) (L((g)^*[ModuleCat.{u + 1} Λ]).obj L)
  have k₁ : (rightDerivedLowerShriekIso Λ
      ((HasCompactification.compactification f).ofIsPullback sq)).hom.app
        (L((g')^*[ModuleCat.{u + 1} Λ]).obj (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj
          (L((f)^*[ModuleCat.{u + 1} Λ]).obj L))) ≫
      (R(f')_![ModuleCat.{u + 1} Λ]).map
        (((leftDerivedUpperStarTensorComparison _ g').app K).app
          (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) =
      (Rf_!((HasCompactification.compactification f).ofIsPullback sq)[ModuleCat.{u + 1} Λ]).map
        (((leftDerivedUpperStarTensorComparison _ g').app K).app
          (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) ≫
      (rightDerivedLowerShriekIso Λ
        ((HasCompactification.compactification f).ofIsPullback sq)).hom.app _ :=
    ((rightDerivedLowerShriekIso Λ
      ((HasCompactification.compactification f).ofIsPullback sq)).hom.naturality _).symm
  have k₂ : (rightDerivedLowerShriekIso Λ
      ((HasCompactification.compactification f).ofIsPullback sq)).hom.app
        (((derivedTensorLeftDerivedUpperStar _ g').obj K).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) ≫
      (R(f')_![ModuleCat.{u + 1} Λ]).map
        (((-⊗ᴸ-(X')[ModuleCat.{u + 1} Λ]).obj (L((g')^*[ModuleCat.{u + 1} Λ]).obj K)).map
          ((derivedSquareUpperStarIso _ sq.toCommSq).inv.app L)) =
      (Rf_!((HasCompactification.compactification f).ofIsPullback sq)[ModuleCat.{u + 1} Λ]).map
        (((-⊗ᴸ-(X')[ModuleCat.{u + 1} Λ]).obj (L((g')^*[ModuleCat.{u + 1} Λ]).obj K)).map
          ((derivedSquareUpperStarIso _ sq.toCommSq).inv.app L)) ≫
      (rightDerivedLowerShriekIso Λ
        ((HasCompactification.compactification f).ofIsPullback sq)).hom.app _ :=
    ((rightDerivedLowerShriekIso Λ
      ((HasCompactification.compactification f).ofIsPullback sq)).hom.naturality _).symm
  simp only [rightDerivedLowerShriekBaseChangeMap, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [← NatTrans.naturality_assoc (rightDerivedLowerShriekIso Λ
    ((HasCompactification.compactification f).ofIsPullback sq)).hom,
    ← NatTrans.naturality (rightDerivedLowerShriekIso Λ
    ((HasCompactification.compactification f).ofIsPullback sq)).hom]
  erw [reassoc_of% thm]
  rw [show rightDerivedLowerShriekIso Λ ((HasCompactification.compactification f).ofIsPullback sq) =
    rightDerivedLowerShriekOfCompactificationIso Λ
      ((HasCompactification.compactification f).ofIsPullback sq)
      (HasCompactification.compactification f') from rfl]
  sorry

end Exchange

end Etale

end AlgebraicGeometry
