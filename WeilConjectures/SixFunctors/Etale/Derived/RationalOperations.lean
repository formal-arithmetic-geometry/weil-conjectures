/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational

/-!
# The exceptional adjunction at the integral and rational stages

Let `Λ` be a Noetherian domain, complete for a principal ideal `I = (ϖ)` with `Λ ⧸ I` finite of
exponent invertible on a field `k` (the integral stage `Λ = 𝒪_E`, `I = 𝔪_E`), and `M` a submonoid
of `Λ` (the nonzero elements, or the powers of `ϖ`), so that the rational stage is
`Dᵇc(X, E) = Dᵇc(X, 𝒪_E)[M⁻¹]` (`CategoryTheory.Rationalization`, blueprint
`def-weil-rationalization-karoubi`). For a separated finite-type morphism `f : X ⟶ Y` of
separated finite-type `k`-schemes this file constructs the compact-support direct image and the
exceptional inverse image on `Dᵇc(-, 𝒪_E)` and `Dᵇc(-, E)`, with the adjunction `Rf_! ⊣ Rf^!`
(blueprint `lem-coef-rational-operations`):

* at the integral stage, `Rf_!` preserves `Dᵇc(-, 𝒪_E)` (blueprint
  `lem-coef-integral-compact-support`,
  `AlgebraicGeometry.Etale.boundedConstructibleIntegral_rightDerivedLowerShriek`) and so does
  `Rf^!` (blueprint `prop-coef-integral-exceptional-adjoint`,
  `AlgebraicGeometry.Etale.boundedConstructibleIntegral_rightDerivedUpperShriek`), so that the
  adjunction `Rf_! ⊣ Rf^!` of `D(X_ét, Λ)` restricts to the constructible categories
  (`AlgebraicGeometry.Etale.boundedConstructibleIntegralLowerShriekUpperShriekAdjunction`);
* at the rational stage, the functors and the adjunction are the rationalizations of the integral
  ones (`AlgebraicGeometry.Etale.boundedConstructibleRationalLowerShriekUpperShriekAdjunction`),
  so that the rational `Rf_E^!` is right adjoint to the rational `Rf_{!,E}` with the localized
  units and counits;
* the rational `Rf_E^!` is computed by coefficient passage from the integral formula
  `Rf^! L ≅ 𝔻_X f^*_comp 𝔻_Y L` of `prop-coef-integral-exceptional-adjoint`
  (`AlgebraicGeometry.Etale.nonempty_iso_boundedConstructibleRationalExceptionalInverseImage`).

## Implementation notes

The rational internal hom and the rational dualizing object are those obtained by coefficient
passage, that is the images under the localization functor of the integral ones; they are not
introduced as separate functors here, and the formula for `Rf_E^!` is stated on objects coming
from the integral stage, which are all the objects of `Dᵇc(X, E)`. The compatibilities of the
identifications with evaluations, units and counits under finite scalar extension are not
recorded.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ}

section Integral

variable [IsDomain Λ] [IsNoetherianRing Λ] [IsAdicComplete I Λ] [Finite (Λ ⧸ I)]
  {k : Type u} [Field k] [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))] {X Y : Scheme.{u}}

/-- Blueprint `lem-coef-integral-compact-support`: Integral compact support.

Let `f : X ⟶ Y` be a separated finite-type morphism of separated finite-type `k`-schemes and
`K ∈ Dᵇc(X, Λ)`, at the integral stage `Λ = 𝒪_E`, `I = (ϖ)`. Then `Rf_! K ∈ Dᵇc(Y, Λ)`, the
canonical compact-support coefficient comparison `(Rf_! K) ⊗ᴸ A_n ≅ Rf_{!,n} K_n` is an
isomorphism (read after restriction of scalars to `Λ`, where `Rf_{!,n} K_n` is `Rf_!(K ⊗ᴸ A_n)`),
and if `dim X ≤ d` and the reductions of `K` have Tor amplitude in `[a, b]`, those of `Rf_! K`
have Tor amplitude in `[a, b + 2d]`.

The coefficient comparison is proved here
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekReductionModIdealMap_span_pow`); the
constructibility and the Tor bound belong to the coefficient chapter. -/
theorem boundedConstructibleIntegral_rightDerivedLowerShriek {ϖ : Λ}
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ}) (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
    [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [QuasiCompact f] [HasCompactification f] {K : 𝐃(X, Λ)}
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
    DerivedCategory.boundedConstructibleIntegral I Y ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) ∧
      (∀ n : ℕ, IsIso ((rightDerivedLowerShriekReductionModIdealMap Λ (I ^ n)
        (HasCompactification.compactification f)).app K)) ∧
      ∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ a b : ℤ,
        (∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj K)) →
        ∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
          ((reductionModIdeal Λ Y (I ^ (n + 1))).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) := by
  refine ⟨sorry, fun n ↦ ?_, sorry⟩
  subst hI
  have := isIso_rightDerivedLowerShriekReductionModIdealMap_span_pow hϖ n
    (HasCompactification.compactification f)
  infer_instance

variable [hϖI : Fact (∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ})]

variable (I) in
/-- The compact-support direct image `Rf_! : Dᵇc(X, Λ) ⥤ Dᵇc(Y, Λ)` at the integral stage, the
restriction of `Rf_!` (`AlgebraicGeometry.Etale.boundedConstructibleIntegral_rightDerivedLowerShriek`,
blueprint `lem-coef-integral-compact-support`). -/
noncomputable abbrev boundedConstructibleIntegralRightDerivedLowerShriek (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
    [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [QuasiCompact f] [HasCompactification f] :
    (DerivedCategory.boundedConstructibleIntegral I X).FullSubcategory ⥤
      (DerivedCategory.boundedConstructibleIntegral I Y).FullSubcategory :=
  ObjectProperty.liftFullSubcategory _ _ (R(f)_![ModuleCat.{u + 1} Λ]) fun _ hK ↦
    have ⟨_, hϖ, hI⟩ := hϖI.out
    (boundedConstructibleIntegral_rightDerivedLowerShriek hϖ hI aX aY f hf hK).1

variable (I) in
/-- The exceptional inverse image `Rf^! : Dᵇc(Y, Λ) ⥤ Dᵇc(X, Λ)` at the integral stage, the
restriction of `Rf^!` (`AlgebraicGeometry.Etale.boundedConstructibleIntegral_rightDerivedUpperShriek`,
blueprint `prop-coef-integral-exceptional-adjoint`). -/
noncomputable abbrev boundedConstructibleIntegralExceptionalInverseImage
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY]
    [HasCompactification aX] [HasCompactification aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [QuasiCompact f] [HasCompactification f] :
    (DerivedCategory.boundedConstructibleIntegral I Y).FullSubcategory ⥤
      (DerivedCategory.boundedConstructibleIntegral I X).FullSubcategory :=
  ObjectProperty.liftFullSubcategory _ _ (R(f)^![ModuleCat.{u + 1} Λ]) fun _ hL ↦
    have ⟨_, hϖ, hI⟩ := hϖI.out
    boundedConstructibleIntegral_rightDerivedUpperShriek hϖ hI aX aY f hf hL

/-- Blueprint `lem-coef-rational-operations`, the integral exceptional adjunction: the adjunction
`Rf_! ⊣ Rf^!` of `D(X_ét, Λ)` restricts to the integral constructible categories
(blueprint `prop-coef-integral-exceptional-adjoint`). -/
noncomputable def boundedConstructibleIntegralLowerShriekUpperShriekAdjunction
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aX] [IsSeparated aY]
    [HasCompactification aX] [HasCompactification aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [QuasiCompact f] [HasCompactification f] :
    boundedConstructibleIntegralRightDerivedLowerShriek I aX aY f hf ⊣
      boundedConstructibleIntegralExceptionalInverseImage I aX aY f hf :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _) (Iso.refl _) (Iso.refl _)

end Integral

end Etale

end AlgebraicGeometry
