/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtensionConstructible
public import WeilConjectures.WeilSheaf.FieldCoefficient

/-!
# From `E`-Weil complexes to `ℚ̄_ℓ`-Weil complexes

Following blueprint `def-weil-weil-sheaf-complex`, the `ℚ̄_ℓ`-stage `D^b_{c,W}(X, ℚ̄_ℓ)` is the
`2`-colimit of the stages `D^b_{c,W}(X, E)` over the finite extensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the
transition functors being the extensions of scalars.
In this repository the `ℚ̄_ℓ`-stage is realised directly, as `AlgebraicGeometry.WeilComplex`
(Weil complexes of modules over the constant sheaf `ℚ̄_ℓ,X̄` of locally finite functions), and the
`E`-stage as `AlgebraicGeometry.FieldWeilComplex` (modules over `E_X̄ : U ↦ C(U, E)`). This file
constructs the functors from the `E`-stages to the `ℚ̄_ℓ`-stage: the extension of scalars
`ℚ̄_ℓ ⊗_E -` of pro-étale sheaves
(`AlgebraicGeometry.ProEtale.fieldExtendScalarsToAdic`) is exact, commutes with the Frobenius
pullbacks (`AlgebraicGeometry.fieldExtendScalarsToAdicFrobeniusIso`) and preserves
constructibility, hence induces an exact functor on pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleFieldWeilSheaf.extendScalarsToAdic`) and a functor
`D^b_{c,W}(X, E) ⥤ D^b_{c,W}(X, ℚ̄_ℓ)` (`AlgebraicGeometry.FieldWeilComplex.extendScalarsToAdic`,
and `AlgebraicGeometry.FieldWeilComplex.toWeilComplex` for a subfield `E ⊆ ℚ̄_ℓ`).

The transition functors between two finite stages `E ⊆ E'`, the cocone of these functors
(`AlgebraicGeometry.FieldWeilComplex.cocone`) and the `2`-colimit
`AlgebraicGeometry.WeilComplexTwoColimit`, with its comparison functor to
`AlgebraicGeometry.WeilComplex`, are in `WeilConjectures.WeilSheaf.FieldCoefficientTransition`
and `WeilConjectures.WeilSheaf.FieldCoefficientTwoColimit`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [Algebra ℚ_[l] Λ] [FiniteDimensional ℚ_[l] Λ] {e : Λ →ₐ[ℚ_[l]] PadicAlgCl l}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

variable [Fact (ringChar k₀ ≠ l)]

section Subfield

variable (E : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E]

end Subfield

end AlgebraicGeometry
