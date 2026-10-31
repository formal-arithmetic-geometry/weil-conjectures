/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CartierKummerData

/-! # Transport of pro-etale scalar units through Cartier realizations

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-lem-geo-cartier/sk-lem-geo-cartier.proof.md`, finite coefficient extension paragraph
(blueprint: lem-amb-cartier-pro-derived-scalar-unit-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor ChangeOfRings
namespace AlgebraicGeometry.Etale
open Scheme

/-- The normalized pro-etale coefficient-reduction property transported through the
Cartier realization data.

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-lem-geo-cartier/sk-lem-geo-cartier.proof.md`, finite coefficient extension paragraph
(blueprint: lem-amb-cartier-pro-derived-scalar-unit-transport).

Proof: conjugate the normalized scalar units by the realization and finite-Tate
comparison isomorphisms; the generator equations are preserved by their normalization,
the defining Hom bijections by composition with isomorphisms, and the Ext equation by
associativity. No flatness or Cartier assumption is used.
-/
/- STATEMENT-DISPUTED: the theorem quantifies over an arbitrary
CartierKummerFamily, but the blueprint statement requires each pair of levels to
carry comparison maps, scalar-unit hypotheses, and an Ext-square hypothesis for
the corresponding classes. Those data are absent from the Lean binders, so the
displayed conclusion cannot be transported for an arbitrary family.
Counterexample (reviewer, 2026-10-30): take a < b, T = 𝔸¹ over an algebraically
closed field of characteristic ≠ l, D the origin, so that by purity
Ext²(i_* A_{a,D}, A_{a,T}(1)) ≅ H⁰(D, A_a) ≠ 0; let c a be a nonzero class there
and c b = 0. The required η satisfies IsCartierDerivedScalarUnit, so
f ↦ η ∘ Res_φ(f) is injective on Hom(G, K) for K = A_{a,T}(1)[2]; then
η ∘ Res_φ(c a) ≠ 0 = c b ∘ θ, and the Ext conclusion fails. The correct statement
carries the node's hypotheses (α_m, q_m, η₀, θ₀, g_m and their Ext square). -/
theorem cartierProDerivedScalarUnitTransport (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : CartierKummerFamily l E) : CartierKummerReduction l E c := by
  sorry

end AlgebraicGeometry.Etale
