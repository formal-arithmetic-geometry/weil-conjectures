/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CoefficientMorphismBasic
public import WeilConjectures.TraceFormula.ContractingGraph
public import WeilConjectures.TraceFormula.ProperCurve

/-!

# The trace formula for Frobenius coefficient morphisms on a proper scheme

For a proper `X` with the model Frobenius `Φ` of a model over a finite field, the trace formula in
degree one holds for every map `ψ : LΦ^* K ⟶ K`
(`ProEtale.CondensedRing.traceFormulaHolds_of_isProper`): the fixed scheme of `Φ` is the disjoint
union of the fixed rational points, the Lefschetz–Verdier formula
(`ProEtale.CondensedRing.Correspondence.trace_globalOperator_eq_sum_localTerm`) writes the trace
as the sum of the local terms, and the graph of the model Frobenius is contracting at its fixed
points, so that each local term is the trace of the stalk map
(`ProEtale.CondensedRing.Correspondence.localTerm_traceClass_ofGraph_eq_trace_of_isContractingAt`).
This is Step 2 of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula` (on `ℙ¹`),
for an arbitrary proper scheme.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

set_option linter.overlappingInstances false in
/-- **The trace formula on a proper scheme** (blueprint
`thm-trf-coefficient-morphism-trace-formula`, Step 2, from `thm-trf-lefschetz-verdier`,
`thm-trf-frobenius-local-term` and `thm-trf-frobenius-fixed-points`): for a proper `X` with the
model Frobenius `Φ` of a model over a finite field, the trace formula in degree one holds. -/
theorem traceFormulaHolds_of_isProper [IsAlgClosed k] [IsProper X.hom] {k₀ : Type u} [Field k₀]
    [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)}
    [LocallyOfFiniteType f₀] {p : X.left ⟶ X₀} {Φ : X ⟶ X} (hΦ : IsModelFrobenius Φ f₀ p)
    [IsProper Φ.left] : TraceFormulaHolds ℓ Φ :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
