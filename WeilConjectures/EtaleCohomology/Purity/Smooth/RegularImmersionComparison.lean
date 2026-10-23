/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Trace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic

/-!
# The smooth-purity comparison for a regular immersion

Let `i : Z ⟶ X` be a closed immersion of codimension `c` between schemes smooth over a field
`k`, with structure morphisms `a_X : X ⟶ Spec k` of relative dimension `n` and
`a_Z = i ≫ a_X` of relative dimension `m`, `m + c = n` (the situation of a regular closed
immersion into a smooth `k`-scheme with regular source, `sk-lem-regular-smooth`). The
comparison

`Φ_i : Λ_Z ≅ Ri^! (Λ_X(c)[2c])`

of blueprint `pur9-rg-def-phi` is assembled from the smooth purity isomorphisms
`Π_{a_X} : Λ_X(n)[2n] ≅ ω_{a_X}` and `Π_{a_Z} : Λ_Z(m)[2m] ≅ ω_{a_Z}`
(`sk-thm-smooth-purity`), the composition comparison `ω_{a_Z} ≅ Ri^! ω_{a_X}` of the exceptional
inverse image, and the passage of the twists through `Ri^!` (`sk-lem-coprojection`). It is the
isomorphism of Steps 1–2 of the proof of `sk-thm-regular`; its existence is
`nonempty_iso_rightDerivedUpperShriek_shiftTateObject_of_isRegularImmersion`.

As in `AlgebraicGeometry.Etale.smoothPurityIso`, the orientations `θ : ω_f ≅ Λ(d)[2d]` of the
two structure morphisms are arguments: the library provides only their existence
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`). Every other ingredient is
the canonical one.

## Main definitions

- `AlgebraicGeometry.Etale.shiftTateObjectTensorNegIso`,
  `AlgebraicGeometry.Etale.shiftTateObjectNegTensorIso`: `Λ(a)[2a]` is invertible, with inverse
  `Λ(-a)[-2a]`.
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekShiftTateObjectIso`: the twist passes through
  `Ri^!`.
- `AlgebraicGeometry.Etale.smoothPurityConstantIso`: `Π_f : Λ_X(d)[2d] ≅ ω_f`.
- `AlgebraicGeometry.Etale.regularImmersionPurityIso`: `Φ_i`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

section Twist

variable (X : Scheme.{u}) [HasInvertibleExponent Λ X]

/-- The tensor inverse of the twist: `Λ_X(a)[2a] ⊗^L Λ_X(-a)[-2a] ≅ Λ_X(0)[0] ≅ Λ_X`, through
`AlgebraicGeometry.Etale.shiftTateObjectAddIso`. -/
noncomputable def shiftTateObjectTensorNegIso (a : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((tateObject Λ X a)⟦2 * a⟧)).obj
        ((tateObject Λ X (-a))⟦2 * -a⟧) ≅ constantComplex Λ X :=
  shiftTateObjectAddIso Λ X a (-a) ≪≫ eqToIso (by rw [add_neg_cancel]) ≪≫
    (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).app _ ≪≫
    HasTateTwist.twistObjectZeroIso (Λ := Λ) X

/-- The tensor inverse of the twist on the other side:
`Λ_X(-a)[-2a] ⊗^L Λ_X(a)[2a] ≅ Λ_X(0)[0] ≅ Λ_X`. -/
noncomputable def shiftTateObjectNegTensorIso (a : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((tateObject Λ X (-a))⟦2 * -a⟧)).obj
        ((tateObject Λ X a)⟦2 * a⟧) ≅ constantComplex Λ X :=
  shiftTateObjectAddIso Λ X (-a) a ≪≫ eqToIso (by rw [neg_add_cancel]) ≪≫
    (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).app _ ≪≫
    HasTateTwist.twistObjectZeroIso (Λ := Λ) X

end Twist

variable {X Y Z : Scheme.{u}}

/-- Blueprint `sk-lem-coprojection`: Co-projection for a closed immersion

*Twists pass through the exceptional inverse image.* For `i : Z ⟶ X`, `K ∈ D(X_ét, Λ)` and
`a ∈ ℤ`,

`Ri^! (K ⊗^L Λ_X(a)[2a]) ≅ Ri^! K ⊗^L Li^*(Λ_X(a)[2a]) ≅ Ri^! K ⊗^L Λ_Z(a)[2a]`:

the co-projection `AlgebraicGeometry.Etale.derivedTensorRightCompRightDerivedUpperShriekIso`
for the invertible object `Λ_X(a)[2a]` with inverse `Λ_X(-a)[-2a]`, followed by
`Li^*(Λ_X(a)[2a]) ≅ Λ_Z(a)[2a]`. -/
noncomputable def rightDerivedUpperShriekShiftTateObjectIso (i : Z ⟶ X) [HasCompactification i]
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Z] (a : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(i)^![ModuleCat.{u + 1} Λ]).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj ((tateObject Λ X a)⟦2 * a⟧)) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj K)).obj
        ((tateObject Λ Z a)⟦2 * a⟧) :=
  (derivedTensorRightCompRightDerivedUpperShriekIso Λ i _ _
      (shiftTateObjectNegTensorIso Λ X a) (shiftTateObjectTensorNegIso Λ X a)).app K ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj _).mapIso (leftDerivedUpperStarTateShiftIso Λ i a)

/-- Blueprint `sk-thm-smooth-purity`: Finite-coefficient smooth purity

The smooth purity isomorphism `Π_f : Λ_X(d)[2d] ≅ Rf^! Λ_Y = ω_f` of a smooth `f : X ⟶ Y` of
relative dimension `d`: the smooth purity map `γ_{f,Λ_Y}` of `def-pur-smooth-purity-map`
(`AlgebraicGeometry.Etale.smoothPurityNatIso`, built from the orientation `θ` and the canonical
tensor comparison) at the constant complex, read through `Lf^* Λ_Y ≅ Λ_X`. -/
noncomputable def smoothPurityConstantIso {d : ℕ} (f : X ⟶ Y) [SmoothOfRelativeDimension d f]
    [HasCompactification f] [HasInvertibleExponent Λ X]
    (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X)) :
    (tateObject Λ X d)⟦2 * (d : ℤ)⟧ ≅ dualizingComplex (ModuleCat.{u + 1} Λ) f :=
  (twistShiftConstantComplexIso Λ X d).symm ≪≫
    (twistShift Λ X d).mapIso (leftDerivedUpperStarConstantComplexIso Λ f).symm ≪≫
    (smoothPurityNatIso Λ (d := d) f θ).app (constantComplex Λ Y)

/-- Blueprint `pur9-rg-def-phi`: The smooth-purity comparison for a regular immersion

Let `i : Z ⟶ X` be a closed immersion and `a_X : X ⟶ Spec k` a structure morphism with
`a_X` smooth of relative dimension `n` and `a_Z = i ≫ a_X` smooth of relative dimension `m`,
`m + c = n` (for a regular closed immersion of codimension `c` with `Z` regular and `X` smooth
over a perfect field, `sk-lem-regular-smooth`,
`AlgebraicGeometry.IsRegularImmersion.smooth_comp`). The comparison

`Φ_i : Λ_Z ≅ Ri^! (Λ_X(c)[2c])`

is the composite of
1. `Λ_Z ≅ Λ_Z(m)[2m] ⊗ Λ_Z(-m)[-2m]` and `Π_{a_Z}` twisted by `(-m)[-2m]`
   (`AlgebraicGeometry.Etale.smoothPurityConstantIso`), giving `ω_{a_Z}(-m)[-2m]`;
2. the composition comparison `c_{a_X,i} : ω_{a_Z} ≅ Ri^! ω_{a_X}` of the exceptional inverse
   image (the conjugate `AlgebraicGeometry.Etale.rightDerivedUpperShriekCompIsoOfLowerShriek` of
   the composition isomorphism `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`),
   twisted by `(-m)[-2m]`;
3. `Ri^! Π_{a_X}⁻¹ : Ri^! ω_{a_X} ≅ Ri^! (Λ_X(n)[2n])`, twisted by `(-m)[-2m]`;
4. the twist `(-m)[-2m]` moved through `Ri^!`
   (`AlgebraicGeometry.Etale.rightDerivedUpperShriekShiftTateObjectIso`, `sk-lem-coprojection`)
   and `Λ_X(n)[2n] ⊗ Λ_X(-m)[-2m] ≅ Λ_X(c)[2c]`, as `n - m = c`.

The twist `(n)[2n]` stays inside `Ri^!` throughout, so it is not moved out and back in. The
blueprint works on one connected component of `X` at a time and assembles over the components;
here `a_X` and `a_Z` are assumed of constant relative dimension, which is the statement on one
component. As in `AlgebraicGeometry.Etale.smoothPurityIso`, the orientations
`θ_X : ω_{a_X} ≅ Λ_X(n)[2n]` and `θ_Z : ω_{a_Z} ≅ Λ_Z(m)[2m]` underlying `Π_{a_X}` and
`Π_{a_Z}` are arguments, the library providing only their existence
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`). -/
noncomputable def regularImmersionPurityIso {k : Type u} [Field k] (c n m : ℕ) (hm : m + c = n)
    (i : Z ⟶ X) [HasCompactification i] (aX : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n aX] [HasCompactification aX]
    [SmoothOfRelativeDimension m (i ≫ aX)] [HasCompactification (i ≫ aX)] [QuasiCompact (i ≫ aX)]
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Z]
    (θX : dualizingComplex (ModuleCat.{u + 1} Λ) aX ≅
      (twistShift Λ X n).obj (constantComplex Λ X))
    (θZ : dualizingComplex (ModuleCat.{u + 1} Λ) (i ≫ aX) ≅
      (twistShift Λ Z m).obj (constantComplex Λ Z)) :
    constantComplex Λ Z ≅
      (R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧) :=
  have hc : (n : ℤ) + -(m : ℤ) = c := by lia
  let tens := derivedTensor (ModuleCat.{u + 1} Λ) Z
  let R := R(i)^![ModuleCat.{u + 1} Λ]
  (shiftTateObjectTensorNegIso Λ Z m).symm ≪≫
    (tens.mapIso (smoothPurityConstantIso Λ (i ≫ aX) θZ ≪≫
      ((rightDerivedUpperShriekCompIsoOfLowerShriek Λ i aX
        (rightDerivedLowerShriekCompIso Λ i aX)).app _).symm ≪≫
      R.mapIso (smoothPurityConstantIso Λ aX θX).symm)).app _ ≪≫
    (rightDerivedUpperShriekShiftTateObjectIso Λ i (-(m : ℤ)) _).symm ≪≫
    R.mapIso (shiftTateObjectAddIso Λ X n (-(m : ℤ))) ≪≫
    eqToIso (by rw [hc])

end Etale

end AlgebraicGeometry
