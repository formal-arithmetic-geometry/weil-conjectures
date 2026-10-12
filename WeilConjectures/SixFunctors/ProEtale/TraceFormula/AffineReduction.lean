/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.RelativeAffineLine

/-!
# The trace formula for affine models

Step 4 of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula`: the trace formula
holds for closed subschemes of `𝔸ⁿ_k`, by induction on `n` through `𝔸ⁿ⁺¹_k ≅ 𝔸¹_{𝔸ⁿ_k}`, and
hence for every affine model of finite type over `k`.

## Main results

- `AlgebraicGeometry.ProEtale.traceFormulaHolds_of_isClosedImmersion_affineSpace`: closed
  subschemes of affine space.
- `AlgebraicGeometry.ProEtale.traceFormulaHolds_of_isAffine`: affine models.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  {k : Type u} [Field k] [Finite k]

/-- Step 4 of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula`: the trace
formula for closed subschemes of the affine space `𝔸ⁿ_k`, by induction on `n` through
`𝔸ⁿ⁺¹_k ≅ 𝔸¹_{𝔸ⁿ_k}` (`traceFormulaHolds_of_isClosedImmersion_relativeAffineLine`), starting
from closed subschemes of `𝔸⁰_k = Spec k`, which are finite over `k`. -/
theorem traceFormulaHolds_of_isClosedImmersion_affineSpace (n : ℕ) {Z₀ : Scheme.{u}}
    (i : Z₀ ⟶ 𝔸(ULift.{u} (Fin n); Spec (.of k))) [IsClosedImmersion i] :
    TraceFormulaHolds A (i ≫ 𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) :=
  sorry

/-- The trace formula for affine models of finite type over `k`: an affine `X₀` of finite type is
a closed subscheme of some `𝔸ⁿ_k` (Steps 1–4 of the proof of blueprint
`thm-trf-coefficient-morphism-trace-formula`). -/
theorem traceFormulaHolds_of_isAffine {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of k)) [IsAffine X₀]
    [LocallyOfFiniteType f₀] : TraceFormulaHolds A f₀ :=
  sorry

end AlgebraicGeometry.ProEtale
