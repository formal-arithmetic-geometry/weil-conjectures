/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceFormulaHolds

/-!
# The trace formula on closed subschemes of a relative affine line

The inductive step of Step 4 of the proof of blueprint
`thm-trf-coefficient-morphism-trace-formula`: the trace formula for closed subschemes of the
relative affine line `𝔸¹_{Y₀}` follows from the trace formula for closed subschemes of `Y₀` and
of affine lines over finite fields, by the Weil `!`-pushforward along the projection to `Y₀`.

## Main results

- `AlgebraicGeometry.ProEtale.traceFormulaHolds_of_isClosedImmersion_relativeAffineLine`.
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

/-- The inductive step of Step 4 of the proof of blueprint
`thm-trf-coefficient-morphism-trace-formula`: let `Y₀` be an affine scheme of finite type over
`k` such that the trace formula holds for all closed subschemes of `Y₀`, and for all closed
subschemes of affine lines over finite fields. Then it holds for all closed subschemes `Z₀` of
the relative affine line `𝔸¹_{Y₀}`: push forward along the projection `Z₀ ⟶ Y₀` with the Weil
`!`-pushforward (`WeilComplex.trace_globalOperator_lowerShriekPush`); its stalk Frobenius at a
fixed point `ȳ` is the degree-one global operator of the fibre over `𝐅_{q^m}`
(`WeilComplex.exists_isModelFrobenius_fibre`), a closed subscheme of the affine line. -/
theorem traceFormulaHolds_of_isClosedImmersion_relativeAffineLine {Y₀ : Scheme.{u}}
    (g₀ : Y₀ ⟶ Spec (.of k)) [IsAffine Y₀] [LocallyOfFiniteType g₀]
    (hY : ∀ {Z₀ : Scheme.{u}} (i : Z₀ ⟶ Y₀) [IsClosedImmersion i], TraceFormulaHolds A (i ≫ g₀))
    (hline : ∀ {k' : Type u} [Field k'] [Finite k'] {Z₀ : Scheme.{u}}
      (i : Z₀ ⟶ 𝔸(PUnit.{u + 1}; Spec (.of k'))) [IsClosedImmersion i],
      TraceFormulaHolds A (i ≫ 𝔸(PUnit.{u + 1}; Spec (.of k')) ↘ Spec (.of k')))
    {Z₀ : Scheme.{u}} (i : Z₀ ⟶ 𝔸(PUnit.{u + 1}; Y₀)) [IsClosedImmersion i] :
    TraceFormulaHolds A (i ≫ 𝔸(PUnit.{u + 1}; Y₀) ↘ Y₀ ≫ g₀) :=
  sorry

end AlgebraicGeometry.ProEtale
