/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix

/-!
# The action of `ℚ̄_ℓ,X` on the sections of an `ℓ`-adic sheaf

Let `F` be a sheaf of `ℚ̄_ℓ,X`-modules on `X_proét` (`AlgebraicGeometry.ProEtale.AdicSheaf`). Its
action `ℚ̄_ℓ,X ⊗ F ⟶ F` is a morphism out of the sheafified tensor product; restricted along the
comparison with the objectwise tensor product it gives, for every object `U`, a bilinear action
`a • x` of the locally finite functions `a ∈ ℚ̄_ℓ,X(U)` on the sections `x ∈ F(U)`
(`AlgebraicGeometry.ProEtale.AdicSheaf.sectionAct`). It is associative and unital, compatible
with restriction and with morphisms of `ℚ̄_ℓ,X`-modules.

A global section `s` of `F` defines the morphism `ℚ̄_ℓ,X ⟶ F`, `a ↦ a • s`
(`AlgebraicGeometry.ProEtale.AdicSheaf.sectionHom`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

variable (F : AdicSheaf l X) {U : X.ProEtᵒᵖ}

end AlgebraicGeometry.ProEtale.AdicSheaf

namespace AlgebraicGeometry.ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}} (F : AdicSheaf l X) {U : X.ProEtᵒᵖ}

open scoped Obj

end AlgebraicGeometry.ProEtale.AdicSheaf
