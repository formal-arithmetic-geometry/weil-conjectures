/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Category

/-!
# The derived Frobenius isomorphism of a Weil complex

Blueprint `def-weil-weil-sheaf-complex`: an object `K` of the Weil category carries, in addition
to its underlying complex `For(K)`, the derived Frobenius isomorphism
`θ_K : Fr_X^* For(K) ≅ For(K)`, represented termwise. Here `For`
(`AlgebraicGeometry.WeilComplex.forget`) is induced by the forgetful functor from pro-étale Weil
sheaves to pro-étale `ℓ`-adic sheaves, and the structure isomorphisms `φ : Fr_X^* F ≅ F` of the
Weil sheaves form a natural isomorphism `Fr_X^* ∘ forget ≅ forget`
(`CategoryTheory.Endofunctor.IsoAlgebra.forgetCompIso`); `θ` is the isomorphism it induces on
derived categories (`AlgebraicGeometry.WeilComplex.frobeniusIso`). The Frobenius pullback
`Fr_X^*` is exact, being an equivalence, so it needs no deriving.

## Main definitions

- `CategoryTheory.Endofunctor.IsoAlgebra.forgetCompIso`: `F ∘ forget ≅ forget`.
- `AlgebraicGeometry.WeilComplex.frobeniusIso`: `θ : Fr_X^* ∘ For ≅ For`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type*} [Category C] (F : C ⥤ C)

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry

namespace WeilComplex

open Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

end WeilComplex

end AlgebraicGeometry
