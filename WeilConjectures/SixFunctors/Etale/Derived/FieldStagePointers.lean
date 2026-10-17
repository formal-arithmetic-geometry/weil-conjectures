/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.RationalStage
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude

/-!
# Properties of the field coefficient stages

Three remarks of blueprint `sk-def-sf-operations` point to properties of the field coefficient
stages proved elsewhere in the blueprint:

* the rationalization `Dᵇc(X, E) = Dᵇc(X, 𝒪_E)[1/ϖ]` is idempotent complete, so that the
  canonical functor into its Karoubi envelope is an equivalence
  (`rem-ptr-weil-rationalization-karoubi-1`, from `lem-weil-rationalization-idempotent-complete`);
* the common-stage category `Dᵇc(X, ℚ̄_ℓ)` is idempotent complete, so that the canonical functor
  into its Karoubi envelope is an equivalence
  (`rem-ptr-weil-algebraically-closed-coefficients-3`, from `lem-weil-qbar-idempotent-complete`);
* at a field coefficient, every bounded constructible complex has finite Tor amplitude, so that
  `Dᵇctf = Dᵇc` (`rem-ptr-weil-finite-tor-amplitude-4`, from `lem-weil-field-tor-amplitude`).

## Implementation notes

* The Karoubi envelopes carry no triangulated structure in this repository, so "exact
  equivalence" is rendered as an equivalence of categories.
* The stage `ℚ̄_ℓ` is `AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleAdic`, the
  Bhatt–Scholze model of the common-stage category.
* The derived tensor product of the field stages is only available, in this repository, for
  étale sheaves of modules over a discrete coefficient field `F`; the Tor amplitude statements
  are made there.
* The lemmas `lem-weil-qbar-idempotent-complete` and `lem-weil-field-tor-amplitude` belong to
  other parts of the blueprint and are only stated here.
-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace AlgebraicGeometry

section Rational

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- Blueprint `rem-ptr-weil-rationalization-karoubi-1`: Pointer to the properties of the
rationalization.

The rationalization `Dᵇc(X, E) = Dᵇc(X, 𝒪_E)[1/ϖ_E]`, in which no idempotent is adjoined, is
nevertheless idempotent complete, so that the canonical functor into its Karoubi envelope is an
equivalence (blueprint `lem-weil-rationalization-idempotent-complete`). -/
theorem Etale.DerivedCategory.isIdempotentComplete_and_isEquivalence_toKaroubi_rational
    (X : Scheme.{u}) :
    IsIdempotentComplete
        (Etale.DerivedCategory.boundedConstructibleRational l E X).FullSubcategory ∧
      (Idempotents.toKaroubi
        (Etale.DerivedCategory.boundedConstructibleRational l E X).FullSubcategory).IsEquivalence :=
  ⟨Etale.DerivedCategory.isIdempotentComplete_boundedConstructibleRational l E X,
    Etale.DerivedCategory.isEquivalence_toKaroubi_boundedConstructibleRational l E X⟩

end Rational

section AlgebraicClosure

variable (l : ℕ) [Fact l.Prime]

/-- Blueprint `lem-weil-qbar-idempotent-complete`: Idempotent completeness of the common-stage
category.

The common-stage category `Dᵇc(X, ℚ̄_ℓ)` (in its Bhatt–Scholze model
`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleAdic`) is idempotent complete. -/
theorem ProEtale.DerivedCategory.isIdempotentComplete_boundedConstructibleAdic
    (X : Scheme.{u}) :
    IsIdempotentComplete (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory :=
  sorry

/-- Blueprint `rem-ptr-weil-algebraically-closed-coefficients-3`: Pointer to the properties of
the common-stage category.

The common-stage category `Dᵇc(X, ℚ̄_ℓ)`, in which no idempotent is adjoined, is nevertheless
idempotent complete, so that the canonical functor into its Karoubi envelope is an equivalence
(blueprint `lem-weil-qbar-idempotent-complete`). -/
theorem ProEtale.DerivedCategory.isIdempotentComplete_and_isEquivalence_toKaroubi_adic
    (X : Scheme.{u}) :
    IsIdempotentComplete (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory ∧
      (Idempotents.toKaroubi
        (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory).IsEquivalence :=
  have := ProEtale.DerivedCategory.isIdempotentComplete_boundedConstructibleAdic l X
  ⟨this, inferInstance⟩

end AlgebraicClosure

section FieldTorAmplitude

variable (F : Type (u + 1)) [Field F] (X : Scheme.{u})

/-- Blueprint `lem-weil-field-tor-amplitude`: Finite Tor amplitude at field coefficients.

For a coefficient field `F`, every bounded constructible complex `K` of étale sheaves of
`F`-modules has finite Tor amplitude: there are `a ≤ b` with `𝓗ʳ(K ⊗ᴸ_F M) = 0` for `r ∉ [a, b]`
and every sheaf `M` of `F`-modules. -/
theorem Etale.DerivedCategory.finiteTorAmplitude_of_boundedConstructible_of_field
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} F))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} F) X K) :
    Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} F) X K :=
  sorry

/-- Blueprint `rem-ptr-weil-finite-tor-amplitude-4`: Pointer to the properties of finite Tor
amplitude.

At a field coefficient `F` the finite-Tor category is the bounded constructible one,
`Dᵇctf(X, F) = Dᵇc(X, F)`, consistently with the amplitude condition: every bounded constructible
complex at a field coefficient has finite Tor amplitude (blueprint
`lem-weil-field-tor-amplitude`). -/
theorem Etale.DerivedCategory.constructibleFiniteTor_eq_boundedConstructible_of_field :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} F) X =
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} F) X := by
  ext K
  exact ⟨fun h ↦ h.1, fun h ↦
    ⟨h, Etale.DerivedCategory.finiteTorAmplitude_of_boundedConstructible_of_field F X h⟩⟩

end FieldTorAmplitude

end AlgebraicGeometry
