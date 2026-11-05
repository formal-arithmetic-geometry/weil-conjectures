/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ConjugatePaste
public import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalarsConstructible

/-!
# Transitivity of the extensions of scalars `E ⊆ E' ⊆ ℚ̄_ℓ`

Let `e : Λ → Λ'` and `e' : Λ' → ℚ̄_ℓ` be continuous `ℚ_ℓ`-algebra maps of finite extensions of
`ℚ_ℓ`. This file identifies the extension of scalars along the composite `e' ∘ e` with the
composite of the extensions of scalars
(`AlgebraicGeometry.ProEtale.fieldExtendScalarsCompExtendScalarsToAdicIso`):

`ℚ̄_ℓ ⊗_Λ - ≅ ℚ̄_ℓ ⊗_{Λ'} (Λ' ⊗_Λ -)`,

the compatibility of the transition functors of blueprint `def-weil-weil-sheaf-complex` with the
functors to the `ℚ̄_ℓ`-stage. It is the conjugate of the identification of the right adjoints
(`AlgebraicGeometry.ProEtale.fieldRestrictScalarsFromAdicCompIso`), restricting scalars along
`Λ_X ⟶ Λ'_X ⟶ ℚ̄_ℓ,X` in two steps or in one, which is the identity on the underlying sheaves.
Since the commutations of the extensions of scalars with the pullbacks are also conjugates of
identities, they paste compatibly
(`AlgebraicGeometry.ProEtale.fieldExtendScalarsCompExtendScalarsToAdicIso_paste`, by
`CategoryTheory.conjugateEquiv_paste`); this is what makes the identification compatible with
the Frobenius structures of Weil sheaves.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

section RestrictScalars

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

variable {R₁ R₂ R₃ : Type (u + 1)} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂)
  (g : R₂ →+* R₃) (X : Scheme.{u})

end RestrictScalars

open scoped Obj

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ] [FiniteDimensional ℚ_[l] Λ'] {e : Λ →ₐ[ℚ_[l]] Λ'}
  {e' : Λ' →ₐ[ℚ_[l]] PadicAlgCl l} (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  (he' : Continuous e') (hc' : Continuous (algebraMap ℚ_[l] Λ'))

variable (X : Scheme.{u})

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X)

section Field

variable {Λ₁ Λ₂ Λ₃ Λ₄ : Type} [NormedField Λ₁] [IsUltrametricDist Λ₁] [NormedField Λ₂]
  [IsUltrametricDist Λ₂] [NormedField Λ₃] [IsUltrametricDist Λ₃] [NormedField Λ₄]
  [IsUltrametricDist Λ₄] [Algebra ℚ_[l] Λ₁] [Algebra ℚ_[l] Λ₂] [Algebra ℚ_[l] Λ₃]
  [Algebra ℚ_[l] Λ₄] [FiniteDimensional ℚ_[l] Λ₂] [FiniteDimensional ℚ_[l] Λ₃]
  [FiniteDimensional ℚ_[l] Λ₄] {e₁ : Λ₁ →ₐ[ℚ_[l]] Λ₂} {e₂ : Λ₂ →ₐ[ℚ_[l]] Λ₃}
  {e₃ : Λ₃ →ₐ[ℚ_[l]] Λ₄} (he₁ : Continuous e₁) (he₂ : Continuous e₂) (he₃ : Continuous e₃)
  (hc₁ : Continuous (algebraMap ℚ_[l] Λ₁)) (hc₂ : Continuous (algebraMap ℚ_[l] Λ₂))
  (hc₃ : Continuous (algebraMap ℚ_[l] Λ₃))

variable (X)

end Field

end AlgebraicGeometry.ProEtale
