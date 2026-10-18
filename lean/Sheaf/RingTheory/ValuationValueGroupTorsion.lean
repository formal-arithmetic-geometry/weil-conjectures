/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Mathlib.RingTheory.Algebraic.Defs

/-! # Algebraic extension gives torsion quotient of value groups

Source: literature/stacks-project/more-algebra.tex, Tag 0ASJ, lemma-etale-extension-valuation-ring,
first proof paragraph (blueprint: lem-trf-valuation-value-group-torsion).
-/

@[expose] public section

universe u v

namespace WeilConjectures

/-- Source: Stacks Tag 0ASJ, lemma-etale-extension-valuation-ring, first proof paragraph;
(blueprint: lem-trf-valuation-value-group-torsion).

For an algebraic extension of fields equipped with a valuation subring, every nonzero
extension element has a positive power equal to a nonzero base element times a unit of
the valuation subring.  The final quotient statement in the source is represented by
this elementwise power-times-unit form.

Proof: choose a nonzero polynomial relation for `x`, normalize it at a term dividing all
other terms, and use closure of the nonunits under addition to force a unit ratio.  The
unit ratio gives the displayed equality, with the two possible orders of the exponents
handled by inversion.  This is the direct polynomial argument recorded in the DAG proof.
-/
theorem algebraic_extension_value_group_torsion
    (K : Type u) (E : Type v) [Field K] [Field E] [Algebra K E]
    [Algebra.IsAlgebraic K E] (V : Subring E)
    (hV : ∀ z : E, z ≠ 0 → z ∈ V ∨ z⁻¹ ∈ V) :
    ∀ x : E, x ≠ 0 →
      ∃ n : ℕ, 0 < n ∧ ∃ a : K, a ≠ 0 ∧ ∃ u : E,
        u ≠ 0 ∧ u ∈ V ∧ u⁻¹ ∈ V ∧ x ^ n = algebraMap K E a * u := by
  sorry

end WeilConjectures
