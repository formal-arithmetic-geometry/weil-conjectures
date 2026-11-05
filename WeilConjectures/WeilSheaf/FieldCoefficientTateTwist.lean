/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.WeilSheaf.FieldCoefficientCohomology
public import WeilConjectures.WeilSheaf.FieldCoefficientTransition
public import WeilConjectures.WeilSheaf.TateTwistCohomology

/-!
# Tate twists commute with extension of scalars

Following blueprint `lem-wf-tate-twist-compatibility`, the Tate twist `(-)(m)` commutes with
finite scalar extension: for finite extensions `E ⊆ F` of `ℚ_ℓ` inside `ℚ̄_ℓ` and `m ∈ ℤ`,

`F ⊗_E E_X(m) ≅ F_X(m)`

compatibly with the Weil structures, and similarly `ℚ̄_ℓ ⊗_E E_X(m) ≅ ℚ̄_ℓ(m)`. Here
`E_X(m)` is the constant `E`-Weil sheaf `E_X` whose Weil structure is multiplied by the
cyclotomic unit `χ_ℓ(σ)ᵐ` (`AlgebraicGeometry.FieldWeilSheaf.tateTwistConstant`).

The proof has three steps.

- The extension of scalars of the constant sheaf is the constant sheaf,
  `Λ' ⊗_Λ Λ_X̄ ≅ Λ'_X̄` (`AlgebraicGeometry.ProEtale.fieldExtendScalarsUnitIso`), and this
  identification is compatible with the canonical Weil structures
  `Fr^* Λ_X̄ = (Fr⁻¹)_* Λ_X̄ ≅ Λ_X̄`. Both identifications are adjoint to the maps on functions
  (composition with `e : Λ → Λ'` and pullback along `Fr`), which commute.
- Extension of scalars along `e` turns multiplication by `b ∈ Λˣ` into multiplication by
  `e(b)`, so it commutes with constant twists.
- The inclusion `E → F` is a `ℚ_ℓ`-algebra map, so it sends the cyclotomic unit of `E` to that
  of `F`.

## Main declarations

- `AlgebraicGeometry.ProEtale.fieldExtendScalars_map_smul`: `Λ' ⊗_Λ (c • -) = e(c) • -`.
- `AlgebraicGeometry.ProEtaleFieldWeilSheaf.constantTwist`: the constant twist of a pro-étale
  `Λ`-Weil sheaf.
- `AlgebraicGeometry.ProEtaleFieldWeilSheaf.extendScalarsConstantTwistIso` and
  `AlgebraicGeometry.ProEtaleFieldWeilSheaf.extendScalarsToAdicConstantTwistIso`: extension of
  scalars commutes with constant twists.
- `AlgebraicGeometry.FieldWeilSheaf.extendScalarsConstantIso`: `Λ' ⊗_Λ Λ_X ≅ Λ'_X` as Weil
  sheaves.
- `AlgebraicGeometry.FieldWeilSheaf.extendScalarsToAdicConstantIso`: `ℚ̄_ℓ ⊗_Λ Λ_X ≅ ℚ̄_ℓ` as
  Weil sheaves.
- `AlgebraicGeometry.FieldWeilSheaf.extendScalarsTateTwistConstantIso`: `F ⊗_E E_X(m) ≅ F_X(m)`.
- `AlgebraicGeometry.FieldWeilSheaf.extendScalarsToAdicTateTwistConstantIso`:
  `ℚ̄_ℓ ⊗_E E_X(m) ≅ ℚ̄_ℓ(m)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

section Field

variable {Λ : Type} [NormedCommRing Λ] [IsUltrametricDist Λ]

end Field

section ExtendScalars

open scoped Obj

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ'] {e : Λ →ₐ[ℚ_[l]] Λ'}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))

end ExtendScalars

section Adic

variable (l : ℕ) [Fact l.Prime]

end Adic

section ExtendScalarsToAdic

open scoped Obj

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [Algebra ℚ_[l] Λ] [FiniteDimensional ℚ_[l] Λ] {e : Λ →ₐ[ℚ_[l]] PadicAlgCl l}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))

end ExtendScalarsToAdic

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

open ProEtale

namespace ProEtaleFieldWeilSheaf

section ConstantTwist

variable {k₀ : Type u} [Field k₀] [Finite k₀] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]

end ConstantTwist

section ExtendScalars

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ'] {e : Λ →ₐ[ℚ_[l]] Λ'}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  (k₀ : Type u) [Field k₀] [Finite k₀]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

end ExtendScalars

section ExtendScalarsToAdic

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [Algebra ℚ_[l] Λ] [FiniteDimensional ℚ_[l] Λ] {e : Λ →ₐ[ℚ_[l]] PadicAlgCl l}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  (k₀ : Type u) [Field k₀] [Finite k₀]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

end ExtendScalarsToAdic

end ProEtaleFieldWeilSheaf

namespace FieldWeilSheaf

section ExtendScalars

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ'] {e : Λ →ₐ[ℚ_[l]] Λ'}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  (k₀ : Type u) [Field k₀] [Finite k₀]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

end ExtendScalars

section ExtendScalarsToAdic

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [Algebra ℚ_[l] Λ] [FiniteDimensional ℚ_[l] Λ] {e : Λ →ₐ[ℚ_[l]] PadicAlgCl l}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  (k₀ : Type u) [Field k₀] [Finite k₀]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

end ExtendScalarsToAdic

section TateTwist

open PadicAlgCl

variable {l : ℕ} [Fact l.Prime] (k₀ : Type u) [Field k₀] [Finite k₀]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [Fact (ringChar k₀ ≠ l)]

end TateTwist

end FieldWeilSheaf

end AlgebraicGeometry
