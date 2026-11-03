/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedFiniteEvaluation.CondensedFiniteFibreEvaluationData

/-! # Existence of finite-fibre evaluation data

The geometric and derived evaluation construction is separated from its Frobenius and
naturality refinements so that the latter can be proved independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj DirectSum
namespace WeilConjectures.CondensedFiniteEvaluation

variable (D : FiniteFieldDatum.{u}) (T₀ : Over (Spec (.of D.k₀))) [IsFinite T₀.hom]
  (l : ℕ) [Fact l.Prime]

/-- The finite geometric fibre admits the canonical evaluation and derived comparison data.

Proof source: the exactness-and-stalks paragraph of
`literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/sec-deligne-laumon-a1/`
`sec-the-weight-bound-on-the-affine-line/sk-thm-dl-a1-upper/lem-zl-finite-pushforward.proof.md`.
Write the finite coordinate algebra, pass to its reduced geometric-point coproduct, and use
exact point sections to identify sections with the finite direct sum.  The same exactness
identifies the right derived functor on degree-zero modules, while constructibility gives
finite-dimensional fibres.  The canonical restriction components define every field of
`Evaluation`, including the H⁰ normalization and its component formula.
(blueprint: lem-zl-condensed-finite-fibre-evaluation-data). -/
theorem finite_fibre_evaluation_data (hl : l ≠ D.p) :
    ∃ E : Evaluation D T₀ l, True := by
  sorry

end WeilConjectures.CondensedFiniteEvaluation
