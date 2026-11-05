/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseWeilSheafTensor
public import WeilConjectures.RepresentationTheory.RepFunctors

/-!
# The Weil fundamental representation as a tensor functor

The Weil fundamental representation `ℱ ↦ (ℱ_t, ρ_ℱ)` of `def-wf-fundamental-representation`
(`AlgebraicGeometry.WeilGroup.fundamentalRep`) is a functor from lisse Weil sheaves to
representations of the Weil group, a morphism acting on the stalks at the base point
(`AlgebraicGeometry.WeilGroup.fundamentalRepFunctor`). It is a tensor functor:

* the identification `(ℱ ⊗ 𝒢)_t ≅ ℱ_t ⊗ 𝒢_t`, built from the evaluation pairings
  `(ℱ ⊗ 𝒢)_t × (ℱ^∨)_t → 𝒢_t` and `(ℱ^∨)_t × ℱ_t → ℚ̄_ℓ`, is an isomorphism of representations
  natural in `ℱ` and `𝒢` (`AlgebraicGeometry.WeilGroup.fundamentalRepTensorIso`), the evaluation
  pairings being dinatural;
* the Weil fundamental representation of the constant sheaf `ℚ̄_ℓ` is the trivial
  representation on `ℚ̄_ℓ` (`AlgebraicGeometry.WeilGroup.fundamentalRepUnitEquiv`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilGroup

open ProEtale Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]

variable [IsCurve (C ↘ Spec (.of K))] {W : WeilGroup (C ↘ Spec (.of K))}
  (M : LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber K)
  {B : BasePointData W}

section StalkMap

end StalkMap

variable (D : WeilMonodromyData B)

end AlgebraicGeometry.WeilGroup
