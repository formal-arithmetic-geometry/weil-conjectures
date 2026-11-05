/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import WeilConjectures.SixFunctors.ProEtale.Adic.SectionAction
public import WeilConjectures.SixFunctors.ProEtale.Adic.TrivialDescent

/-!
# Trivialising an `ℓ`-adic sheaf by global sections

Global sections `s₁, …, sᵣ` of a sheaf `F` of `ℚ̄_ℓ,X`-modules define the morphism
`ℚ̄_ℓ,Xʳ ⟶ F`, `(aᵢ) ↦ ∑ aᵢ • sᵢ` (`AlgebraicGeometry.ProEtale.AdicSheaf.ofSections`). It is an
isomorphism as soon as, for every object `U` of `X_proét`, every section of `F` over `U` is
uniquely of the form `∑ aᵢ • sᵢ|_U` with `aᵢ ∈ ℚ̄_ℓ,X(U)`
(`AlgebraicGeometry.ProEtale.AdicSheaf.isIso_ofSections`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}} (F : AdicSheaf l X) {r : ℕ}
  (s : Fin r → F.X.obj.obj (op (proEtTop X)))

end AlgebraicGeometry.ProEtale.AdicSheaf
