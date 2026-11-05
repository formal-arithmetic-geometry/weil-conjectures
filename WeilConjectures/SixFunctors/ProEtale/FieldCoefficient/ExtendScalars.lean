/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtension

/-!
# Extension of scalars between finite extensions of `ℚ_ℓ`

Let `Λ`, `Λ'` be fields with an ultrametric norm which are `ℚ_ℓ`-algebras, `Λ'` being
finite-dimensional over `ℚ_ℓ`, and let `e : Λ → Λ'` be a continuous `ℚ_ℓ`-algebra map; the case
of interest is an inclusion `E ⊆ E'` of finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, the transition
functors of the `2`-colimit `D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)` of blueprint
`def-weil-weil-sheaf-complex`. This file constructs the extension of scalars

`Λ' ⊗_Λ - : Sh(X_proét, Λ_X) ⥤ Sh(X_proét, Λ'_X)`

between sheaves of modules over the constant sheaves `Λ_X : U ↦ C(U, Λ)` and
`Λ'_X : U ↦ C(U, Λ')` (`AlgebraicGeometry.ProEtale.fieldExtendScalars`), exactly as the
extension of scalars to `ℚ̄_ℓ` of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtension`.

Composing with `e` is a morphism of sheaves of rings `Λ_X ⟶ Λ'_X`
(`AlgebraicGeometry.ProEtale.fieldConstantSheafToRestrictScalarsField`), whose adjoint
`Λ' ⊗_Λ Λ_X ⟶ Λ'_X` is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_extendScalarsFieldConstantSheafHomField`): it is injective on
sections, `Λ'` being free over the field `Λ`, and surjective on sections, a continuous function
`f : U → Λ'` being the finite sum `∑ₖ bₖ · cₖ ∘ f` for a `ℚ_ℓ`-basis `(bₖ)` of `Λ'` with
(continuous) coordinate functions `cₖ`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

open scoped Obj

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ'] (e : Λ →ₐ[ℚ_[l]] Λ')

variable {e} (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
include he

variable (X : Scheme.{u})

end AlgebraicGeometry.ProEtale
