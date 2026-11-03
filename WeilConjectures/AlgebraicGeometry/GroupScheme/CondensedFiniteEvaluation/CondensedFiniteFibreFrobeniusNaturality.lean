/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedFiniteEvaluation.CondensedFiniteFibreEvaluationData

/-! # Frobenius and naturality refinements of finite-fibre evaluation

This module records the independent orbit, return-map, and naturality part of the
finite-fibre argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj DirectSum
namespace WeilConjectures.CondensedFiniteEvaluation

variable (D : FiniteFieldDatum.{u}) (T₀ : Over (Spec (.of D.k₀))) [IsFinite T₀.hom]
  (l : ℕ) [Fact l.Prime]

/-- Every canonical evaluation datum has the Frobenius orbit and naturality refinements.

Proof source: the Frobenius-orbit, local-return, and naturality paragraphs of
`literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/sec-deligne-laumon-a1/`
`sec-the-weight-bound-on-the-affine-line/sk-thm-dl-a1-upper/lem-zl-finite-pushforward.proof.md`.
The geometric Frobenius acts on residue-field embeddings by one cyclic permutation in each
closed-point block.  Pullback composition coherences and the Weil isomorphism give the
transport square; iterating it through the cycle gives the local return operator.  The same
coherences prove naturality for module maps and semilinear isomorphisms, and the H⁰
normalization transports the action to the derived comparison.
(blueprint: lem-zl-condensed-finite-fibre-frobenius-naturality). -/
theorem finite_fibre_frobenius_naturality (hl : l ≠ D.p) (E : Evaluation D T₀ l)
    (hE : True) : Nonempty (Frobenius D T₀ l E) ∧ Naturality D T₀ l E := by
  sorry

end WeilConjectures.CondensedFiniteEvaluation
