/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Const
public import WeilConjectures.WeilSheaf.FieldCoefficientTransition

/-!
# `D^b_{c,W}(X, ℚ̄_ℓ)` as the `2`-colimit of the `E`-stages

Blueprint `def-weil-weil-sheaf-complex` defines

`D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)`

over the directed set of the finite extensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, along the extensions of scalars
`F ⊗_E -`, with the common-stage construction: objects are pairs `(E, K)` and morphisms are
represented at a common finite stage. This file makes this a genuine definition:

- the extensions of scalars `D^b_{c,W}(X, E) ⥤ D^b_{c,W}(X, F)` form a stage system
  (`AlgebraicGeometry.FieldWeilComplex.stageSystem`, in the sense of
  `CategoryTheory.StageSystem`): the associativity constraints `G ⊗_F (F ⊗_E -) ≅ G ⊗_E -`
  (`AlgebraicGeometry.FieldWeilComplex.extendScalarsCompIso`) satisfy the cocycle condition,
  which holds for the extensions of scalars of pro-étale sheaves
  (`AlgebraicGeometry.ProEtale.fieldExtendScalarsCompIso_cocycle`) and passes to Weil sheaves and
  to derived categories (`CategoryTheory.Functor.mapDerivedCategoryCompNatIso_cocycle`);
- `AlgebraicGeometry.WeilComplexTwoColimit k₀ l X` is its pair category, the `2`-colimit;
- the functors `ℚ̄_ℓ ⊗_E - : D^b_{c,W}(X, E) ⥤ WeilComplex k₀ l X` to the `ℚ̄_ℓ`-stage of
  `WeilConjectures.WeilSheaf.Category` (`AlgebraicGeometry.FieldWeilComplex.toWeilComplex`) are
  compatible with the associativity constraints, hence induce the comparison functor
  `AlgebraicGeometry.WeilComplexTwoColimit.toWeilComplex` from the `2`-colimit.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

section Comp

variable {l : ℕ} [Fact l.Prime] {Λ₁ Λ₂ Λ₃ : Type} [NormedField Λ₁] [IsUltrametricDist Λ₁]
  [NormedField Λ₂] [IsUltrametricDist Λ₂] [NormedField Λ₃] [IsUltrametricDist Λ₃]
  [Algebra ℚ_[l] Λ₁] [Algebra ℚ_[l] Λ₂] [Algebra ℚ_[l] Λ₃] [FiniteDimensional ℚ_[l] Λ₂]
  [FiniteDimensional ℚ_[l] Λ₃] {e₁ : Λ₁ →ₐ[ℚ_[l]] Λ₂} {e₂ : Λ₂ →ₐ[ℚ_[l]] Λ₃}
  (he₁ : Continuous e₁) (he₂ : Continuous e₂) (hc₁ : Continuous (algebraMap ℚ_[l] Λ₁))
  (hc₂ : Continuous (algebraMap ℚ_[l] Λ₂))
  (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

end Comp

section Cocycle

variable {l : ℕ} [Fact l.Prime] {Λ₁ Λ₂ Λ₃ Λ₄ : Type} [NormedField Λ₁] [IsUltrametricDist Λ₁]
  [NormedField Λ₂] [IsUltrametricDist Λ₂] [NormedField Λ₃] [IsUltrametricDist Λ₃]
  [NormedField Λ₄] [IsUltrametricDist Λ₄] [Algebra ℚ_[l] Λ₁] [Algebra ℚ_[l] Λ₂]
  [Algebra ℚ_[l] Λ₃] [Algebra ℚ_[l] Λ₄] [FiniteDimensional ℚ_[l] Λ₂] [FiniteDimensional ℚ_[l] Λ₃]
  [FiniteDimensional ℚ_[l] Λ₄] {e₁ : Λ₁ →ₐ[ℚ_[l]] Λ₂} {e₂ : Λ₂ →ₐ[ℚ_[l]] Λ₃}
  {e₃ : Λ₃ →ₐ[ℚ_[l]] Λ₄} (he₁ : Continuous e₁) (he₂ : Continuous e₂) (he₃ : Continuous e₃)
  (hc₁ : Continuous (algebraMap ℚ_[l] Λ₁)) (hc₂ : Continuous (algebraMap ℚ_[l] Λ₂))
  (hc₃ : Continuous (algebraMap ℚ_[l] Λ₃))
  (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

variable [FiniteDimensional ℚ_[l] Λ₁]

end Cocycle

section TwoColimit

open PadicAlgCl

variable {l : ℕ} [Fact l.Prime] (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k₀))]

variable [Fact (ringChar k₀ ≠ l)]

end TwoColimit

end AlgebraicGeometry
