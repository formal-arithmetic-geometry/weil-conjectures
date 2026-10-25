/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients

/-!
# Verdier biduality at the integral stage

Let `Λ` be a Noetherian domain, complete for a principal ideal `I = (ϖ)` with `Λ ⧸ I` finite of
exponent invertible on an algebraically closed field `k` (the integral stage `Λ = 𝒪_E`,
`I = 𝔪_E`), and `X` separated of finite type over `k` with structure morphism `a_X`. The integral
dualizing complex `ω_{X, 𝒪_E} = R lim_n Res_n Ra_{X,n}^! A_n` is the point of a homotopy limit
cone of the tower `n ↦ Ra_X^!(Λ ⧸ Iⁿ)` (restriction of scalars commuting with `Ra_X^!`), and the
integral Verdier dual is `𝔻_X = RHom(-, ω_X)`. This file records the integral stage of blueprint
`thm-sf-biduality-class` (`AlgebraicGeometry.Etale.verdierDual_integralStage`), deduced, as in the
blueprint, from integral Verdier duality (`thm-coef-integral-verdier`,
`AlgebraicGeometry.Etale.boundedConstructibleIntegral_derivedHom_dualizing`), which belongs to the
coefficient chapter.

## Implementation notes

As elsewhere in the repository
(`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`), the Tor amplitude of
the reductions `K ⊗ᴸ Λ ⧸ Iⁿ⁺¹` is measured over `Λ`, after restriction of scalars. Since
`Λ ⧸ Iⁿ⁺¹ ⊗ᴸ_Λ Λ ⧸ Iⁿ⁺¹ ≅ Λ ⧸ Iⁿ⁺¹ ⊕ Λ ⧸ Iⁿ⁺¹[1]`, a Tor interval `[a, b]` over `Λ` of the
restriction of an `A_n`-complex is the interval `[a + 1, b]` over `A_n`, and conversely `[α, β]`
over `A_n` gives `[α - 1, β]` over `Λ`. The finite-stage dual interval `[-b - 2d, -a]` of the
blueprint therefore reads `[-b - 2d - 1, -a - 1]` in this convention.

The exceptional inverse image `Ra_X^!` over `Λ` is the right adjoint of `Ra_{X!}`, so it is defined
under the hypothesis that `Ra_{X!}` is a left adjoint, taken as an instance argument (it is a
theorem for torsion coefficients, `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

attribute [local instance] derivedBraidedCategory

section DoubleDual

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

/-- The double-dual morphism `δ_K : K ⟶ RHom(RHom(K, ω), ω)` into an arbitrary object `ω` of
`D(X_ét)`, written with `AlgebraicGeometry.Etale.derivedHom`: it is
`CategoryTheory.MonoidalClosed.toIhomIhom` for the derived braiding. Stating results at a
concrete coefficient ring through this constant keeps the instance-found monoidal closed
structure out of their types (see `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`). -/
noncomputable def derivedHomDoubleDual
    (ω K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    K ⟶ ((derivedHom A X).obj (op (((derivedHom A X).obj (op K)).obj ω))).obj ω :=
  MonoidalClosed.toIhomIhom ω K

lemma derivedHomDoubleDual_eq (ω K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    derivedHomDoubleDual A X ω K = MonoidalClosed.toIhomIhom ω K :=
  rfl

end DoubleDual

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) [IsDomain Λ] [IsNoetherianRing Λ]
  [IsAdicComplete I Λ] [Finite (Λ ⧸ I)] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  (hI : I = Ideal.span {ϖ}) {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
  [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
  [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]

include hϖ hI in
/-- Blueprint `prop-coef-integral-dualizing`: The integral dualizing object and its adjunction.

For `a_X : X ⟶ Spec k` separated of finite type, `k` algebraically closed, there is a derived
complete object `ω_{X, 𝒪_E} = R lim_n Res_n Ra_{X,n}^! A_n`, realised as the point of a homotopy
limit cone `ω` of the tower `n ↦ Ra_X^!(Λ ⧸ Iⁿ)` (restriction of scalars commuting with
`Ra_X^!`), such that:

1. its reductions are `ω ⊗ᴸ A_n ≅ Ra_X^!(Λ ⧸ Iⁿ)`;
2. `ω ∈ Dᵇc(X, 𝒪_E)`, and if `dim X ≤ d` its reductions have Tor amplitude in `[-2d - 1, 0]`
   (the interval `[-2d, 0]` of the blueprint, measured over `A_n`; see the module
   documentation);
3. for `K ∈ Dᵇc(X, 𝒪_E)` there is an isomorphism of derived mapping complexes
   `Ra_{X*} RHom(K, ω) ≅ RHom(Ra_{X!} K, Λ)`. -/
theorem exists_isHomotopyLimit_dualizing :
    ∃ ω : Cone (DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
        R(aX)^![Λ]), Pretriangulated.IsHomotopyLimit ω ∧
      (∀ n : ℕ, Nonempty ((reductionModIdeal Λ X (I ^ n)).obj ω.pt ≅
        (R(aX)^![Λ]).obj
          ((DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I).obj (op n)))) ∧
      DerivedCategory.boundedConstructibleIntegral I X ω.pt ∧
      (∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ n : ℕ,
        DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-2 * (d : ℤ) - 1) 0
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj ω.pt)) ∧
      ∀ K : 𝐃(X, Λ), DerivedCategory.boundedConstructibleIntegral I X K →
        Nonempty ((R((aX)_*[ModuleCat.{u + 1} Λ])).obj
            (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj ω.pt) ≅
          ((derivedHom (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
            (op ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K))).obj (constantComplex Λ (Spec (.of k)))) :=
  sorry

variable
  (ωX : Cone (DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I ⋙
    R(aX)^![Λ]))
  (hωX : Pretriangulated.IsHomotopyLimit ωX)

include hϖ hI hωX in
/-- Blueprint `thm-coef-integral-verdier`: Integral Verdier duality.

For `K ∈ Dᵇc(X, 𝒪_E)` and the integral dualizing complex `ω_X` (the point of a homotopy limit
cone of `n ↦ Ra_X^!(Λ ⧸ Iⁿ)`), the integral Verdier dual `𝔻_X K = RHom(K, ω_X)`:

1. lies in `Dᵇc(X, 𝒪_E)`;
2. has reductions `(𝔻_X K) ⊗ᴸ A_n ≅ 𝔻_{X,n} K_n`, read after restriction of scalars as
   `RHom(K, Ra_X^!(Λ ⧸ Iⁿ))`;
3. if `dim X ≤ d` and the reductions of `K` have Tor amplitude in `[a, b]`, the reductions of
   `𝔻_X K` have Tor amplitude in `[-b - 2d - 1, -a - 1]` (the interval `[-b - 2d, -a]` of the
   blueprint, measured over `A_n`; see the module documentation);
4. the double-dual map `δ_K : K ⟶ 𝔻_X 𝔻_X K` is an isomorphism. -/
theorem boundedConstructibleIntegral_derivedHom_dualizing {K : 𝐃(X, Λ)}
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
    DerivedCategory.boundedConstructibleIntegral I X
        (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj ωX.pt) ∧
      (∀ n : ℕ, Nonempty ((reductionModIdeal Λ X (I ^ n)).obj
          (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj ωX.pt) ≅
        ((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj ((R(aX)^![Λ]).obj
          ((DerivedCategory.quotPowFunctor (Spec (.of k)).smallEtaleTopology I).obj (op n))))) ∧
      (∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ a b : ℤ,
        (∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj K)) →
        ∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X
          (-b - 2 * (d : ℤ) - 1) (-a - 1)
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj
            (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj ωX.pt))) ∧
      IsIso (derivedHomDoubleDual (ModuleCat.{u + 1} Λ) X ωX.pt K) :=
  sorry

include hϖ hI hωX in
/-- Blueprint `thm-sf-biduality-class`: Verdier biduality on the coefficient class, at the
integral stage `Λ = 𝒪_E`.

For `X` separated of finite type over an algebraically closed field `k`, the integral Verdier
dual `𝔻_X = RHom(-, ω_X)` preserves `Dᵇc(X, 𝒪_E)` (which is `Dᵇc_ctf(X, 𝒪_E)`, the uniform Tor
bound being part of its definition) and the double-dual map `δ_K : K ⟶ 𝔻_X 𝔻_X K` is an
isomorphism on it, so that `𝔻_X` is an exact anti-equivalence of `Dᵇc(X, 𝒪_E)`; the uniform
reduction Tor interval `[a, b]` gives `[-b - 2d - 1, -a - 1]` for the dual (measured over `Λ`).
As in the blueprint this is integral Verdier duality
(`AlgebraicGeometry.Etale.boundedConstructibleIntegral_derivedHom_dualizing`). The finite stages
are `AlgebraicGeometry.Etale.verdierDual_finiteStage`. -/
theorem verdierDual_integralStage :
    (∀ {K : 𝐃(X, Λ)}, DerivedCategory.boundedConstructibleIntegral I X K →
      DerivedCategory.boundedConstructibleIntegral I X
          (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj ωX.pt) ∧
        IsIso (derivedHomDoubleDual (ModuleCat.{u + 1} Λ) X ωX.pt K)) ∧
    ∀ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ (a b : ℤ) {K : 𝐃(X, Λ)},
      DerivedCategory.boundedConstructibleIntegral I X K →
      (∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj K)) →
      ∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X
        (-b - 2 * (d : ℤ) - 1) (-a - 1)
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj
          (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj ωX.pt)) :=
  ⟨fun hK ↦ ⟨(boundedConstructibleIntegral_derivedHom_dualizing I hϖ hI aX ωX hωX hK).1,
      (boundedConstructibleIntegral_derivedHom_dualizing I hϖ hI aX ωX hωX hK).2.2.2⟩,
    fun d hd a b _ hK hab ↦
      (boundedConstructibleIntegral_derivedHom_dualizing I hϖ hI aX ωX hωX hK).2.2.1 d hd a b hab⟩

end Etale

end AlgebraicGeometry
