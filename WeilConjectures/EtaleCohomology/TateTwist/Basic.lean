/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleSheafPowers
public import WeilConjectures.SixFunctors.Etale.Derived.PullbackIntTensorFamily
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction

/-!
# The Tate twists

Let `Λ` be a commutative ring of positive characteristic `n`. This file constructs the Tate
twists `Λ_X(m)`, `m ∈ ℤ`, of the blueprint (`def-coefficient-twists-detailed`) on every scheme
`X` on which `n` is invertible, and shows that they form a Tate twist datum
(`AlgebraicGeometry.Etale.HasTateTwist`) for the coefficient ring `Λ`.

## Construction

On the universal base `S = Spec ℤ[1/n]` (`AlgebraicGeometry.invertibleExponentBase`) the Tate
sheaf `Λ_S(1) = μₙ ⊗ Λ` (`AlgebraicGeometry.Etale.tateSheaf`) becomes the constant sheaf `Λ` on
the étale cover `V ⟶ S` adjoining a primitive `n`-th root of unity
(`AlgebraicGeometry.Etale.tateCover`), so its dual is a tensor inverse
(`AlgebraicGeometry.Etale.tateSheafTensorInverse`). Its integer tensor powers in `D(S_ét, Λ)` form
a coherent family `Λ_S(m)` (`AlgebraicGeometry.Etale.tateIntTensorFamily`): `Λ_S(m)` is the
`m`-th tensor power of `Λ_S(1)` for `m ≥ 0` and of its dual for `m < 0`, placed in degree zero.
On a scheme `X` on which `n` is invertible, `Λ_X(m)` is the derived pullback of `Λ_S(m)` along
the unique morphism `X ⟶ S` (`AlgebraicGeometry.Etale.tateTwistObject`); all compatibilities
between the twists of different schemes are then those of the derived pullbacks. On the other
schemes, which play no role, `Λ_X(m)` is defined to be `Λ_X`.

## Main definitions

- `AlgebraicGeometry.Etale.tateTwistObject`: the twisting objects `Λ_X(m)`.
- `AlgebraicGeometry.Etale.hasTateTwist`: the Tate twist datum.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The characteristic of `Λ` is invertible in `ℤ[1/n]`. -/
lemma isUnit_ringChar_invertibleExponentRing :
    IsUnit ((ringChar Λ : ℕ) : InvertibleExponentRing.{u} Λ) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (ringChar Λ : ℤ))
    (ringChar Λ : ℤ)
  let φ : Localization.Away (ringChar Λ : ℤ) →+* InvertibleExponentRing.{u} Λ :=
    ULift.ringEquiv.symm.toRingHom
  simpa using h.map φ

/-- The ring `ℤ[1/n][ζ]` of the cover `V` of `Spec ℤ[1/n]` adjoining a primitive `n`-th root of
unity. -/
noncomputable abbrev tateCoverRing : CommRingCat.{u} :=
  .of (PrimitiveRootsAlgebra (InvertibleExponentRing.{u} Λ) (ringChar Λ))

/-- The étale cover `V ⟶ Spec ℤ[1/n]` adjoining a primitive `n`-th root of unity, `n` being the
characteristic of `Λ`. -/
noncomputable abbrev tateCover : Spec (tateCoverRing Λ) ⟶ invertibleExponentBase.{u} Λ :=
  primitiveRootsCover _ _

variable [NeZero (ringChar Λ)]

instance etale_tateCover : Etale (tateCover Λ) :=
  etale_primitiveRootsCover _ _ (NeZero.ne _) (isUnit_ringChar_invertibleExponentRing Λ)

lemma surjective_tateCover : Function.Surjective (tateCover Λ).base :=
  surjective_primitiveRootsCover _ _ (isUnit_ringChar_invertibleExponentRing Λ)

/-- The primitive root of unity `ζ` on the cover `V`. -/
noncomputable def tateCoverZeta : Γ(Spec (tateCoverRing Λ), ⊤)ˣ :=
  ((PrimitiveRootsAlgebra.isUnit_zeta _ _ (Nat.pos_of_ne_zero (NeZero.ne _))).map
    (Scheme.ΓSpecIso (tateCoverRing Λ)).inv.hom).unit

lemma tateCoverZeta_pow : tateCoverZeta Λ ^ ringChar Λ = 1 := by
  ext
  simp only [tateCoverZeta, Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one,
    ← map_pow, PrimitiveRootsAlgebra.zeta_pow, map_one]

lemma isUnit_tateCoverZeta_pow_sub {i j : ℕ} (hi : i < ringChar Λ) (hj : j < ringChar Λ)
    (hij : i ≠ j) :
    IsUnit (((tateCoverZeta Λ : _) : Γ(Spec (tateCoverRing Λ), ⊤)) ^ i -
      ((tateCoverZeta Λ : _) : Γ(Spec (tateCoverRing Λ), ⊤)) ^ j) := by
  simpa [tateCoverZeta, ← map_pow, ← map_sub] using
    (PrimitiveRootsAlgebra.isUnit_zeta_pow_sub_zeta_pow _ _ hi hj hij).map
      (Scheme.ΓSpecIso (tateCoverRing Λ)).inv.hom

/-- The Tate sheaf of `Spec ℤ[1/n]` becomes the constant sheaf `Λ` on the cover `V`. -/
noncomputable def upperStarTateCoverTateSheafIso :
    (tateCover Λ)^*[ModuleCat.{u + 1} Λ].obj (tateSheaf Λ (invertibleExponentBase.{u} Λ)) ≅
      𝟙_ _ :=
  asIso (upperStarTateSheafToTateSheaf Λ (tateCover Λ)) ≪≫
    tateSheafIsoConstantSheaf _ (tateCoverZeta Λ) (tateCoverZeta_pow Λ)
      (fun _ hi _ hj hij ↦ isUnit_tateCoverZeta_pow_sub Λ hi hj hij)

/-- The dual of the Tate sheaf of `Spec ℤ[1/n]` is a tensor inverse: the Tate sheaf is trivial
on the étale cover `V`. -/
noncomputable def tateSheafTensorInverse :
    TensorInverse (tateSheaf Λ (invertibleExponentBase.{u} Λ)) :=
  tensorInverseOfUpperStarIso (ModuleCat.{u + 1} Λ) (fun _ : Unit ↦ tateCover Λ)
    (by rw [Set.iUnion_const]; exact Set.range_eq_univ.2 (surjective_tateCover Λ)) _
    (fun _ ↦ upperStarTateCoverTateSheafIso Λ)

/-- The coherent family of the Tate twists `Λ_S(m)` on `S = Spec ℤ[1/n]`: the integer tensor
powers of the Tate sheaf `Λ_S(1)`, placed in degree zero. -/
noncomputable def tateIntTensorFamily :=
  (tateSheafTensorInverse Λ).singleFunctor.intTensorFamily


open Classical in
/-- Blueprint `def-coefficient-twists-detailed`: Coefficient Tate twists.

The Tate twisting object `Λ_X(m) ∈ D(X_ét, Λ)`: on a scheme `X` on which the characteristic `n`
of `Λ` is invertible, the derived pullback of `Λ_S(m)`
(`AlgebraicGeometry.Etale.tateIntTensorFamily`) along the unique morphism `X ⟶ S = Spec ℤ[1/n]`.
It is the sheaf `(μₙ ⊗ Λ)^{⊗ m}` for `m ≥ 0`, and its dual `Hom((μₙ ⊗ Λ)^{⊗ -m}, Λ)` for
`m < 0`, placed in degree zero. On the other schemes it is `Λ_X`. -/
noncomputable def tateTwistObject (X : Scheme.{u}) (m : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  if h : HasInvertibleExponent Λ X then
    haveI := h
    (pullbackIntTensorFamily (ModuleCat.{u + 1} Λ) (tateIntTensorFamily Λ)
      (toInvertibleExponentBase (Λ := Λ) X)).obj m
  else constantComplex Λ X

lemma tateTwistObject_eq (X : Scheme.{u}) [HasInvertibleExponent Λ X] :
    tateTwistObject Λ X = (pullbackIntTensorFamily (ModuleCat.{u + 1} Λ) (tateIntTensorFamily Λ)
      (toInvertibleExponentBase (Λ := Λ) X)).obj :=
  funext fun _ ↦ dif_pos _

/-- The coherent family of the Tate twists `Λ_X(m)` on a scheme `X` on which the characteristic
of `Λ` is invertible. -/
noncomputable def tateTwistIntTensorFamily (X : Scheme.{u}) [HasInvertibleExponent Λ X] :=
  (pullbackIntTensorFamily (ModuleCat.{u + 1} Λ) (tateIntTensorFamily Λ)
    (toInvertibleExponentBase (Λ := Λ) X)).copy (tateTwistObject Λ X) (tateTwistObject_eq Λ X)

section Fields

variable (X : Scheme.{u}) [HasInvertibleExponent Λ X]

/-- `Λ_X(0) ≅ Λ_X`. -/
noncomputable def tateTwistObjectZeroIso : tateTwistObject Λ X 0 ≅ constantComplex Λ X :=
  (tateTwistIntTensorFamily Λ X).zeroIso

/-- `Λ_X(m) ⊗ᴸ Λ_X(m') ≅ Λ_X(m + m')`. -/
noncomputable def tateTwistObjectAddIso (m m' : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (tateTwistObject Λ X m)).obj
      (tateTwistObject Λ X m') ≅ tateTwistObject Λ X (m + m') :=
  (tateTwistIntTensorFamily Λ X).derivedTensorAddIso m m'

lemma isInvertible_tateTwistObject (m : ℤ) :
    DerivedCategory.isInvertible Λ X (tateTwistObject Λ X m) :=
  (tateTwistIntTensorFamily Λ X).exists_derivedTensor_iso m

lemma tateTwistObjectAddIso_zero_left (m : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).map (tateTwistObjectZeroIso Λ X).hom).app
        (tateTwistObject Λ X m) ≫ (derivedTensorLeftUnitor _ X (tateTwistObject Λ X m)).hom =
      (tateTwistObjectAddIso Λ X 0 m).hom ≫ eqToHom (by rw [zero_add]) :=
  (tateTwistIntTensorFamily Λ X).derivedTensor_zero_left m

lemma tateTwistObjectAddIso_zero_right (m : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (tateTwistObject Λ X m)).map
        (tateTwistObjectZeroIso Λ X).hom ≫
        (derivedTensorRightUnitor _ X (tateTwistObject Λ X m)).hom =
      (tateTwistObjectAddIso Λ X m 0).hom ≫ eqToHom (by rw [add_zero]) :=
  (tateTwistIntTensorFamily Λ X).derivedTensor_zero_right m

lemma tateTwistObjectAddIso_assoc (a b c : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).map (tateTwistObjectAddIso Λ X a b).hom).app
        (tateTwistObject Λ X c) ≫ (tateTwistObjectAddIso Λ X (a + b) c).hom =
      (derivedTensorAssociator _ X (tateTwistObject Λ X a) (tateTwistObject Λ X b)
          (tateTwistObject Λ X c)).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (tateTwistObject Λ X a)).map
          (tateTwistObjectAddIso Λ X b c).hom ≫ (tateTwistObjectAddIso Λ X a (b + c)).hom ≫
            eqToHom (by rw [add_assoc]) :=
  (tateTwistIntTensorFamily Λ X).derivedTensor_assoc a b c

end Fields

section Pullback

variable {X Y Z : Scheme.{u}} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

/-- The identification `Lf^* Λ_Y(m) ≅ Λ_X(m)` of the Tate twists, through the composition
isomorphism of the derived pullbacks along `X ⟶ Y ⟶ S`. -/
noncomputable def leftDerivedUpperStarTateTwistObjectIso (f : X ⟶ Y) (m : ℤ) :
    L((f)^*[ModuleCat.{u + 1} Λ]).obj (tateTwistObject Λ Y m) ≅ tateTwistObject Λ X m :=
  pullbackIntTensorFamilyCopyIso _ _ (tateTwistObject Λ X) (tateTwistObject Λ Y) f
    (toInvertibleExponentBase X) (toInvertibleExponentBase Y)
    (comp_toInvertibleExponentBase f).symm (tateTwistObject_eq Λ X) (tateTwistObject_eq Λ Y) m

lemma leftDerivedUpperStarTateTwistObjectIso_comp [HasInvertibleExponent Λ Z] (f : X ⟶ Y)
    (g : Y ⟶ Z) (m : ℤ) :
    leftDerivedUpperStarTateTwistObjectIso Λ (f ≫ g) m =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g).app (tateTwistObject Λ Z m) ≪≫
        (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarTateTwistObjectIso Λ g m) ≪≫
          leftDerivedUpperStarTateTwistObjectIso Λ f m :=
  pullbackIntTensorFamilyCopyIso_comp _ _ (tateTwistObject Λ X) (tateTwistObject Λ Y)
    (tateTwistObject Λ Z) f g (toInvertibleExponentBase X) (toInvertibleExponentBase Y)
    (toInvertibleExponentBase Z) (comp_toInvertibleExponentBase (f ≫ g)).symm
    (comp_toInvertibleExponentBase g).symm (comp_toInvertibleExponentBase f).symm
    (tateTwistObject_eq Λ X) (tateTwistObject_eq Λ Y) (tateTwistObject_eq Λ Z) m

lemma leftDerivedUpperStar_map_tateTwistObjectAddIso (f : X ⟶ Y) (m m' : ℤ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (tateTwistObjectAddIso Λ Y m m').hom ≫
        (leftDerivedUpperStarTateTwistObjectIso Λ f (m + m')).hom =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) f _ _).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).map
          (leftDerivedUpperStarTateTwistObjectIso Λ f m).hom).app _ ≫
          ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (tateTwistObject Λ X m)).map
            (leftDerivedUpperStarTateTwistObjectIso Λ f m').hom ≫
            (tateTwistObjectAddIso Λ X m m').hom :=
  map_addIso_pullbackIntTensorFamilyCopyIso _ _ (tateTwistObject Λ X) (tateTwistObject Λ Y) f
    (toInvertibleExponentBase X) (toInvertibleExponentBase Y)
    (comp_toInvertibleExponentBase f).symm (tateTwistObject_eq Λ X) (tateTwistObject_eq Λ Y)
    m m'

end Pullback

end Etale

end AlgebraicGeometry
