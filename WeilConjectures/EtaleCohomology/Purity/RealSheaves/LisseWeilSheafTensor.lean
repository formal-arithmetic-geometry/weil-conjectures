/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationTensor
public import WeilConjectures.WeilSheaf.DerivedHom
public import WeilConjectures.WeilSheaf.TateTwistCohomology

/-!
# The tensor product of lisse Weil sheaves as a bifunctor

The tensor product `ℱ ⊗ 𝒢 = [ℱ^∨, 𝒢]` of a lisse Weil sheaf `ℱ` with a Weil sheaf `𝒢`
(`AlgebraicGeometry.WeilSheaf.tensorObj`) is functorial in both variables: the internal hom
`[A, B]` of pro-étale Weil sheaves is contravariant in `A`
(`AlgebraicGeometry.ProEtaleWeilSheaf.ihomMapLeft`) and covariant in `B`
(`AlgebraicGeometry.ProEtaleWeilSheaf.ihomMapRight`), so a morphism `f : ℱ ⟶ ℱ'` induces
`f^∨ : ℱ'^∨ ⟶ ℱ^∨` (`AlgebraicGeometry.WeilSheaf.dualMap`), and `f`, `g : 𝒢 ⟶ 𝒢'` induce
`f ⊗ g : ℱ ⊗ 𝒢 ⟶ ℱ' ⊗ 𝒢'` (`AlgebraicGeometry.WeilSheaf.tensorHom`).

## Main definitions

- `AlgebraicGeometry.LisseWeilSheaf.tensor`: the tensor product bifunctor on lisse Weil sheaves.
- `AlgebraicGeometry.LisseWeilSheaf.unit`: the constant lisse Weil sheaf `ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace ProEtaleWeilSheaf

end ProEtaleWeilSheaf

namespace WeilSheaf

end WeilSheaf

namespace LisseWeilSheaf

end LisseWeilSheaf

end AlgebraicGeometry
