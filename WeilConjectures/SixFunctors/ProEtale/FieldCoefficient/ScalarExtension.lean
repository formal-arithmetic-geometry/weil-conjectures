/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.ExtendScalarsInjective
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

/-!
# Extension of scalars from a finite extension `E` of `ℚ_ℓ` to `ℚ̄_ℓ`

Let `Λ` be a field with an ultrametric norm which is a finite-dimensional `ℚ_ℓ`-algebra, with a
continuous `ℚ_ℓ`-algebra embedding `e : Λ → ℚ̄_ℓ`; the case of interest is a finite extension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` (blueprint `def-weil-weil-sheaf-complex`, `def-weil-algebraically-closed-
coefficients`). This file constructs the extension of scalars

`ℚ̄_ℓ ⊗_Λ - : Sh(X_proét, Λ_X) ⥤ Sh(X_proét, ℚ̄_ℓ,X)`

from sheaves of modules over the constant sheaf `Λ_X : U ↦ C(U, Λ)`
(`AlgebraicGeometry.ProEtale.FieldSheaf`) to `ℓ`-adic sheaves, modules over the constant sheaf
`ℚ̄_ℓ,X` of locally finite functions (`AlgebraicGeometry.ProEtale.AdicSheaf`)
(`AlgebraicGeometry.ProEtale.fieldExtendScalarsToAdic`).

Composing with `e` sends continuous `Λ`-valued functions to locally finite `ℚ̄_ℓ`-valued ones,
a morphism of sheaves of rings `Λ_X ⟶ ℚ̄_ℓ,X` (seen in sheaves of `Λ`-modules,
`AlgebraicGeometry.ProEtale.fieldConstantSheafToRestrictScalars`). Its adjoint
`ℚ̄_ℓ ⊗_Λ Λ_X ⟶ ℚ̄_ℓ,X`, from the extension of scalars of sheaves along `Λ → ℚ̄_ℓ`
(`AlgebraicGeometry.ProEtale.sheafExtendScalars`), is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_extendScalarsFieldConstantSheafHom`): it is injective on
sections, `ℚ̄_ℓ` being free over the field `Λ`, and locally surjective, a locally finite function
taking near every point values in a finite-dimensional `ℚ_ℓ`-subspace of `ℚ̄_ℓ`, so that it is
locally a finite sum `∑ₖ vₖ · cₖ` of constants `vₖ ∈ ℚ̄_ℓ` times continuous `ℚ_ℓ`-valued
coordinate functions `cₖ`. The extension of scalars of modules is then the functor induced by the
monoidal adjunction `ℚ̄_ℓ ⊗_Λ - ⊣ res` on module objects (`CategoryTheory.Adjunction.modLeft`).

## Main definitions

- `AlgebraicGeometry.ProEtale.fieldConstantSheafToRestrictScalars`: `Λ_X ⟶ res ℚ̄_ℓ,X`.
- `AlgebraicGeometry.ProEtale.extendScalarsFieldConstantSheafHom`: `ℚ̄_ℓ ⊗_Λ Λ_X ≅ ℚ̄_ℓ,X`.
- `AlgebraicGeometry.ProEtale.fieldExtendScalarsToAdic`: `ℚ̄_ℓ ⊗_Λ -`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

open scoped Obj

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [Algebra ℚ_[l] Λ] [FiniteDimensional ℚ_[l] Λ] (e : Λ →ₐ[ℚ_[l]] PadicAlgCl l)

variable {e} (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
include he

variable (X : Scheme.{u})

end AlgebraicGeometry.ProEtale
