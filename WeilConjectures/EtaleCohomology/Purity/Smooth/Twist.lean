/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# Twist-and-shift identifications

Elementary identifications for the twist-and-shift functor `K ↦ K(m)[2m]`
(`AlgebraicGeometry.Etale.twistShift`) of the purity conventions: its value on the constant
complex, the zero twist, its compatibility with pullback, the additivity of twists, and the
reassociation `M(m)[2m] ≅ M ⊗ Λ(m)[2m]`. All shifts are even, so no sign is involved.

## Main definitions

- `AlgebraicGeometry.Etale.twistShiftConstantComplexIso`: `Λ_X(m)[2m] ≅ Λ_X(m)[2m]`.
- `AlgebraicGeometry.Etale.twistShiftZeroIso`: `K(0)[0] ≅ K`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarTwistShiftIso`: `Lf^*(K(m)[2m]) ≅ (Lf^* K)(m)[2m]`.
- `AlgebraicGeometry.Etale.twistShiftTwistShiftIso`:
  `(K(m)[2m])(m')[2m'] ≅ K(m + m')[2(m + m')]`.
- `AlgebraicGeometry.Etale.twistShiftObjIso`: `M(m)[2m] ≅ M ⊗ Λ_X(m)[2m]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

section Twists

variable {X Y : Scheme.{u}} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

/-- `Λ_X(m)[2m] = (Λ_X ⊗^L Λ_X(m))[2m] ≅ Λ_X(m)[2m]`, through the left unitor. -/
noncomputable def twistShiftConstantComplexIso (X : Scheme.{u}) (m : ℤ) :
    (twistShift Λ X m).obj (constantComplex Λ X) ≅ (tateObject Λ X m)⟦2 * m⟧ :=
  (shiftFunctor _ (2 * m)).mapIso (derivedTensorLeftUnitor _ X _)

/-- The zero twist is trivial: `K(0)[0] ≅ K`. -/
noncomputable def twistShiftZeroIso (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    {m : ℤ} (hm : m = 0)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (twistShift Λ X m).obj K ≅ K :=
  (shiftFunctorZero' _ (2 * m) (by simp [hm])).app _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).mapIso
      (eqToIso (by rw [hm]; rfl) ≪≫ HasTateTwist.twistObjectZeroIso X) ≪≫
    derivedTensorRightUnitor _ X K

/-- Pullback commutes with twist-and-shift, `Lf^*(K(m)[2m]) ≅ (Lf^* K)(m)[2m]`. -/
noncomputable def leftDerivedUpperStarTwistShiftIso (f : X ⟶ Y) (m : ℤ)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).obj ((twistShift Λ Y m).obj K) ≅
      (twistShift Λ X m).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  ((L((f)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * m)).app _ ≪≫
    (shiftFunctor _ (2 * m)).mapIso
      (leftDerivedUpperStarTensorIso _ f K (tateObject Λ Y m) ≪≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj _).mapIso
          (leftDerivedUpperStarTateObjectIso f m))

/-- Twist-and-shifts compose additively, `(K(m)[2m])(m')[2m'] ≅ K(m + m')[2(m + m')]`. All
shifts are even, so no sign is involved. -/
noncomputable def twistShiftTwistShiftIso (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    (m m' : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (twistShift Λ X m').obj ((twistShift Λ X m).obj K) ≅ (twistShift Λ X (m + m')).obj K :=
  (shiftFunctor _ (2 * m')).mapIso
      ((((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj (tateObject Λ X m')).commShiftIso
        (2 * m)).app _) ≪≫
    ((shiftFunctorAdd' _ (2 * m) (2 * m') (2 * (m + m')) (by ring)).app _).symm ≪≫
    (shiftFunctor _ (2 * (m + m'))).mapIso
      (derivedTensorAssociator _ X _ _ _ ≪≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).mapIso
          (HasTateTwist.twistObjectAddIso X m m'))

omit [HasInvertibleExponent Λ Y] in
/-- `Lf^* K (m)[2m]` lies in `D^b_{ctf}` when `K` does. -/
theorem boundedConstructibleFiniteTor_twistShift_leftDerivedUpperStar (f : X ⟶ Y) (m : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    DerivedCategory.boundedConstructibleFiniteTor Λ X
      ((twistShift Λ X m).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) :=
  DerivedCategory.boundedConstructibleFiniteTor.shift
    (constructibleFiniteTor_tensor _ X (constructibleFiniteTor_leftDerivedUpperStar _ f hK)
      (boundedConstructibleFiniteTor_tateObject Λ X m)) _

end Twists

section Twist

variable {X : Scheme.{u}} [HasInvertibleExponent Λ X]

variable (X) in
/-- Blueprint `def-coefficient-twists-detailed`: the twist reassociation

`M(m)[2m] = (M ⊗ Λ_X(m))[2m] ≅ M ⊗ Λ_X(m)[2m]`,

moving the shift into the twisting factor (`M ⊗ -` commutes with shifts) and reading
`Λ_X(m)[2m]` as the twist-and-shift of `Λ_X`. All shifts are even, so no sign occurs. -/
noncomputable def twistShiftObjIso (m : ℤ)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (twistShift Λ X m).obj M ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).obj
        ((twistShift Λ X m).obj (constantComplex Λ X)) :=
  ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).commShiftIso (2 * m)).app
      (tateObject Λ X m)).symm ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).mapIso (twistShiftConstantComplexIso Λ X m).symm

variable (X) in
omit [Finite Λ] [HasInvertibleExponent Λ X] in
/-- The twist reassociation `M(m)[2m] ≅ M ⊗ Λ_X(m)[2m]` is natural in `M`. This rests on the
naturality of the shift compatibility of `M ⊗ᴸ -` in the fixed factor `M`
(`AlgebraicGeometry.Etale.derivedTensor_map_app_comp_commShiftIso_hom_app`). -/
@[reassoc]
lemma twistShift_map_comp_twistShiftObjIso_hom (m : ℤ)
    {M M' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (g : M ⟶ M') :
    (twistShift Λ X m).map g ≫ (twistShiftObjIso Λ X m M').hom =
      (twistShiftObjIso Λ X m M).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).map g).app _ := by
  have h := derivedTensor_map_app_comp_commShiftIso_hom_app _ g (2 * m) (tateObject Λ X m)
  have h' : (((derivedTensor (ModuleCat.{u + 1} Λ) X).map g).app (tateObject Λ X m))⟦2 * m⟧' ≫
      ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M').commShiftIso (2 * m)).inv.app
        (tateObject Λ X m)) =
      ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).commShiftIso (2 * m)).inv.app
        (tateObject Λ X m)) ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).map g).app ((tateObject Λ X m)⟦2 * m⟧) := by
    rw [← cancel_epi ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).commShiftIso
      (2 * m)).hom.app (tateObject Λ X m)), Iso.hom_inv_id_app_assoc, ← reassoc_of% h,
      Iso.hom_inv_id_app]
    exact Category.comp_id _
  dsimp only [twistShiftObjIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
  rw [Category.assoc, NatTrans.naturality]
  exact (reassoc_of% h') _

end Twist

end Etale

end AlgebraicGeometry
