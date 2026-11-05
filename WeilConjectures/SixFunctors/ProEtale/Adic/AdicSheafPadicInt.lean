/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafRing
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntExtendScalars

/-!
# `ℓ`-adic sheaves as `ℤ_ℓ,X`-modules

The inclusion `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X` of ring objects of abelian sheaves on `X_proét`, followed by the
comparison of the two models of `ℚ̄_ℓ,X`, is a morphism of ring objects
`ℤ_ℓ,X ⟶ ℚ̄_ℓ,X = adicConstantSheaf ℓ X`
(`AlgebraicGeometry.ProEtale.padicIntSheafToAdicConstantSheaf`), the target being viewed as a ring
object of abelian sheaves through the lax monoidal forgetful functor `weilCoefficientsForgetAb`.
Restricting scalars along it, an `ℓ`-adic sheaf is a module object over `ℤ_ℓ,X` in abelian
sheaves (`AlgebraicGeometry.ProEtale.AdicSheaf.restrictPadicInt`). Extension of scalars
`M ↦ ℚ̄_ℓ,X ⊗_{ℤ_ℓ,X} M` along it is left adjoint to restriction of scalars
(`AlgebraicGeometry.ProEtale.padicIntExtendScalarsAdicConstantSheafAdjunction`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

end AlgebraicGeometry.ProEtale
