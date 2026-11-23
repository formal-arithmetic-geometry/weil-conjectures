/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FieldCoefficientExtendScalars
public import WeilConjectures.WeilSheaf.FieldCoefficientTransition

/-!
# Extension of scalars of constructible `E`-Weil sheaves

The extensions of scalars `Λ' ⊗_Λ -` and `ℚ̄_ℓ ⊗_Λ -` of pro-étale Weil sheaves preserve
constructibility, so they restrict to functors between the categories of constructible Weil
sheaves. These are the sheaf-level counterparts of
`AlgebraicGeometry.FieldWeilComplex.extendScalars` and
`AlgebraicGeometry.FieldWeilComplex.extendScalarsToAdic`.

## Main definitions

- `AlgebraicGeometry.FieldWeilSheaf.extendScalarsToAdic`: `ℚ̄_ℓ ⊗_Λ -` from constructible
  `Λ`-Weil sheaves to constructible `ℚ̄_ℓ`-Weil sheaves, and
  `AlgebraicGeometry.FieldWeilSheaf.toWeilSheaf` for a subfield `E ⊆ ℚ̄_ℓ`.
- `AlgebraicGeometry.FieldWeilSheaf.extendScalars`: `Λ' ⊗_Λ -` on constructible Weil sheaves, and
  `AlgebraicGeometry.FieldWeilSheaf.transition` for finite extensions `E ⊆ F` inside `ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open ProEtale

section ToAdic

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [Algebra ℚ_[l] Λ] [FiniteDimensional ℚ_[l] Λ] {e : Λ →ₐ[ℚ_[l]] PadicAlgCl l}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  (k₀ : Type u) [Field k₀] [Finite k₀] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The extension of scalars `ℚ̄_ℓ ⊗_Λ -` from constructible `Λ`-Weil sheaves to constructible
`ℚ̄_ℓ`-Weil sheaves. -/
noncomputable def FieldWeilSheaf.extendScalarsToAdic :
    FieldWeilSheaf k₀ Λ X ⥤ WeilSheaf k₀ l X :=
  (FieldWeilSheaf.objectProperty k₀ Λ X).liftFullSubcategory (WeilSheaf.objectProperty k₀ l X)
    (ProEtaleFieldWeilSheaf.extendScalarsToAdic he hc k₀ X)
    fun _ hF ↦ hF.extendScalarsToAdic he hc

variable (E : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E]

/-- The extension of scalars `ℚ̄_ℓ ⊗_E -` from constructible `E`-Weil sheaves to constructible
`ℚ̄_ℓ`-Weil sheaves, for a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
noncomputable def FieldWeilSheaf.toWeilSheaf : FieldWeilSheaf k₀ E X ⥤ WeilSheaf k₀ l X :=
  FieldWeilSheaf.extendScalarsToAdic (e := E.val) continuous_subtype_val
    (PadicAlgCl.continuous_algebraMap_intermediateField E) k₀ X

end ToAdic

section Transition

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ'] {e : Λ →ₐ[ℚ_[l]] Λ'}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The extension of scalars `Λ' ⊗_Λ -` of constructible Weil sheaves. -/
noncomputable def FieldWeilSheaf.extendScalars :
    FieldWeilSheaf k₀ Λ X ⥤ FieldWeilSheaf k₀ Λ' X :=
  (FieldWeilSheaf.objectProperty k₀ Λ X).liftFullSubcategory
    (FieldWeilSheaf.objectProperty k₀ Λ' X)
    (ProEtaleFieldWeilSheaf.extendScalars he hc k₀ X)
    fun _ hF ↦ hF.extendScalars he hc

/-- The extension of scalars `F ⊗_E -` of constructible Weil sheaves, for finite extensions
`E ⊆ F` of `ℚ_ℓ` inside `ℚ̄_ℓ`. -/
noncomputable def FieldWeilSheaf.transition {E F : PadicAlgCl.FiniteIntermediateField l}
    (h : E ≤ F) : FieldWeilSheaf k₀ E.1 X ⥤ FieldWeilSheaf k₀ F.1 X :=
  FieldWeilSheaf.extendScalars (PadicAlgCl.continuous_inclusion_finiteIntermediateField h)
    (PadicAlgCl.continuous_algebraMap_intermediateField E.1) k₀ X

end Transition

end AlgebraicGeometry
