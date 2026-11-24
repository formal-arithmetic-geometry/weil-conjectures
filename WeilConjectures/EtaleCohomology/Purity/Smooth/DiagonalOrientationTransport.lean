/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionTwistShiftTransport
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierDualWeil
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction
/-!
# The induced morphism of fibre squares and the pullback of the twist-and-shift

A square `g' ≫ f = f' ≫ g` induces `e : X' ×_{Y'} X' ⟶ X ×_Y X`
(`AlgebraicGeometry.Etale.IsoSquare.map`), along which the base change of the canonical
orientation is computed (`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange`).
The pullback comparison `Le^*(Λ_Y(m)[2m]) ≅ Λ_X(m)[2m]` is the pullback of the twist-and-shift
followed by the twist-and-shift of `Le^* Λ_Y ≅ Λ_X`
(`AlgebraicGeometry.Etale.twistShiftConstantComplexBaseChangeIso_hom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

namespace IsoSquare

variable {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : IsPullback g' f' f g)

/-- The morphism `X' ×_{Y'} X' ⟶ X ×_Y X` induced by a square `g' ≫ f = f' ≫ g`. -/
noncomputable abbrev map : pullback f' f' ⟶ pullback f f :=
  pullback.map f' f' f f g' g' g sq.w.symm sq.w.symm

end IsoSquare

section Twist

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

/-- The pullback comparison `Le^*(Λ_Y(m)[2m]) ≅ Λ_X(m)[2m]` of
`AlgebraicGeometry.Etale.twistShiftConstantComplexBaseChangeIso` is the pullback of the
twist-and-shift (`AlgebraicGeometry.Etale.leftDerivedUpperStarTwistShiftIso`) followed by the
twist-and-shift of `Le^* Λ_Y ≅ Λ_X`. -/
lemma twistShiftConstantComplexBaseChangeIso_hom (e : X ⟶ Y) (m : ℤ) :
    (twistShiftConstantComplexBaseChangeIso Λ e m).hom =
      (leftDerivedUpperStarTwistShiftIso Λ e m (constantComplex Λ Y)).hom ≫
        (twistShift Λ X m).map (leftDerivedUpperStarUnitIso _ e).hom := by
  have hn := (L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso_hom_naturality
    (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) Y (tateObject Λ Y m)).hom (2 * m)
  have h := leftDerivedUpperStar_map_derivedTensorLeftUnitor_hom (A := ModuleCat.{u + 1} Λ) e
    (tateObject Λ Y m)
  rw [derivedTensor_map_app, ← leftDerivedUpperStarUnitIso_hom_eq_η] at h
  have hu : 𝟙_ _ ◁ (leftDerivedUpperStarTateObjectIso e m).hom ≫
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X _).hom =
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X _).hom ≫
          (leftDerivedUpperStarTateObjectIso e m).hom :=
    leftUnitor_naturality _
  have hin : (L((e)^*[ModuleCat.{u + 1} Λ])).map
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) Y (tateObject Λ Y m)).hom ≫
        (leftDerivedUpperStarTateObjectIso e m).hom ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X (tateObject Λ X m)).inv =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) e (constantComplex Λ Y)
          (tateObject Λ Y m)).hom ≫
        _ ◁ (leftDerivedUpperStarTateObjectIso e m).hom ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) e).hom ▷ tateObject Λ X m := by
    rw [h, Category.assoc, Category.assoc, ← reassoc_of% hu, Iso.hom_inv_id, Category.comp_id,
      whisker_exchange]
    rfl
  simp only [twistShiftConstantComplexBaseChangeIso, leftDerivedUpperStarTwistShiftIso,
    leftDerivedUpperStarTateShiftIso, twistShiftConstantComplexIso, twistShift, tateTwist,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom,
    Functor.comp_map, Functor.flip_obj_map, derivedTensor_obj_map, derivedTensor_map_app,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← Functor.map_comp, ← Functor.map_comp, hin, Functor.map_comp,
    Functor.map_comp]
  rfl

end Twist

end AlgebraicGeometry.Etale
