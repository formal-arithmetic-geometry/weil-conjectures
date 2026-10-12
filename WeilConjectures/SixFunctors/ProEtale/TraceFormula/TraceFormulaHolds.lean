/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.ModelRestriction
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Perfectness
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardFibres

/-!
# The trace formula on finite models and on closed subschemes of the affine line

Steps 1–3 of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula`, the statement
`TF(X₀, K, φ, m)` of the trace formula for a model `X₀` over a finite field `k`, and its proof
for finite models (Step 1), for the affine line (Step 2) and for closed subschemes of the affine
line (Step 3), which are the line itself or finite over `k`.

## Main definitions

- `AlgebraicGeometry.ProEtale.TraceFormulaHolds`: the trace formula holds for every Weil complex
  with model `f₀ : X₀ ⟶ Spec k`, in every degree `m ≥ 1`.

## Main results

- `AlgebraicGeometry.ProEtale.traceFormulaHolds_of_isFinite`: Step 1, finite models.
- `AlgebraicGeometry.ProEtale.traceFormulaHolds_affineLine`: Step 2, the affine line.
- `AlgebraicGeometry.ProEtale.traceFormulaHolds_of_isClosedImmersion_affineLine`: Step 3, closed
  subschemes of the affine line.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- The trace formula `TF(X₀, K, φ, m)` holds for the model `f₀ : X₀ ⟶ Spec k`: for every
algebraically closed field `Ω` over `k`, every Weil complex `(K, φ)` with `K ∈ Dᵇctf` on
`X = X₀ ×_{Spec k} Spec Ω` whose Frobenius is the base change of the `q`-power Frobenius of `X₀`,
and every `m ≥ 1`, the trace formula `WeilComplex.TraceFormula` holds (notation of the proof of
blueprint `thm-trf-coefficient-morphism-trace-formula`, Step 0). -/
def TraceFormulaHolds {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (.of k)) : Prop :=
  ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (G : GeometricOperations A (Spec (.of Ω)))
    {X : Scheme.{u}} {aX : X ⟶ Spec (.of Ω)} [IsGeometric aX] [HasCompactification aX]
    {W : WeilComplex (A := A) aX} {σ : Spec (.of Ω) ⟶ Spec (.of k)} {p : X ⟶ X₀},
    W.IsModelFrobenius f₀ σ p → ∀ (hctf : G.ctf X W.obj) (m : ℕ), 1 ≤ m →
      ∀ [IsProper (W.graph G hctf m).snd], W.TraceFormula G hctf m

variable {A} {k : Type u} [Field k] [Finite k]

/-- The trace formula is invariant under isomorphisms of models. -/
theorem TraceFormulaHolds.of_iso {X₀ X₀' : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k)}
    (e : X₀' ≅ X₀) (h : TraceFormulaHolds A f₀) : TraceFormulaHolds A (e.hom ≫ f₀) :=
  sorry

/-- Step 1 of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula`: the trace
formula for finite models `X₀ ⟶ Spec k`. The geometric base change `X` is a finite disjoint union
of local Artinian schemes, `RΓ_c(X, K)` is the sum of the geometric stalks by topological
invariance, and the global operator is a block matrix whose diagonal blocks are the stalk
Frobenius maps at the fixed points. -/
theorem traceFormulaHolds_of_isFinite {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of k)) [IsFinite f₀] :
    TraceFormulaHolds A f₀ :=
  sorry

/-- Step 2 of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula`: the trace
formula for the affine line `𝔸¹_k`, through its compactification `𝔸¹ ⊆ ℙ¹`
(blueprint `lem-trf-compactification-graph-operator`), the Lefschetz–Verdier formula on `ℙ¹`
and the Frobenius local terms on the smooth curve `ℙ¹`. -/
theorem traceFormulaHolds_affineLine :
    TraceFormulaHolds A (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) :=
  sorry

/-- Step 3 of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula`: the trace
formula for closed subschemes of the affine line `𝔸¹_k`. A closed subscheme `Spec k[t]/I` is the
line itself if `I = 0` (Step 2), and finite over `k` otherwise (Step 1). -/
theorem traceFormulaHolds_of_isClosedImmersion_affineLine {Z₀ : Scheme.{u}}
    (i : Z₀ ⟶ 𝔸(PUnit.{u + 1}; Spec (.of k))) [IsClosedImmersion i] :
    TraceFormulaHolds A (i ≫ 𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) :=
  sorry

end AlgebraicGeometry.ProEtale
