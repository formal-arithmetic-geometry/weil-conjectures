/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Equality of valuation topologies and common coarsenings

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé XX, section 4.4,
printed page 374, valued-field background. The criterion and its elementary proof are the
agent-selected refinement recorded in the DAG, not a theorem quoted from ILO.
(blueprint: lem-per-valuation-topology-common-coarsening)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace AddValuation

/-- Two nontrivial additive valuations induce the same topology exactly when their valuation
subrings lie in a common proper valuation subring of the field.

Source: ILO, Travaux de Gabber, Exposé XX, section 4.4, printed page 374, valued-field
background; the following elementary proof is the agent proof recorded in the DAG.
(blueprint: lem-per-valuation-topology-common-coarsening)

`WithTop Γᵢ` is `Γᵢ ∪ {∞}`. The associated multiplicative valuation reverses the order,
so its integer ring is precisely `{x | 0 ≤ vᵢ x}`, and its topology has the balls
`{x | (γ : WithTop Γᵢ) < vᵢ (x - a)}` as a basis. The surjectivity hypotheses identify the
finite values with the stated value groups. A common nontrivial coarsening means exactly
the proper valuation subring in the conclusion; equality of the two integer rings is not
asserted. There is no henselianity, rank, or completeness assumption.

Proof:
1. The valuation inequalities make each integer ring `Vᵢ` a subring, and for every nonzero
   `x`, either `x` or its inverse is in `Vᵢ`. Nontriviality supplies a positive finite value
   `εᵢ`. Surjectivity supplies a value `-εᵢ`, so `Vᵢ` is proper. The ball of threshold zero
   lies in `Vᵢ`, making it a zero-neighbourhood.
2. If the topologies agree, a second-valuation ball of threshold `δ` lies in `V₁`. Choose
   nonzero `a` with `v₂(a) = δ + ε₂`. Then `a V₂ ⊆ V₁` by multiplicativity.
3. Let `S` be the subring of finite sums of products `x y`, with `x ∈ V₁`, `y ∈ V₂`,
   including the empty sum. Concatenation, negation and distribution show it is a subring
   containing both rings. Also `a S ⊆ V₁`, so `S = K` would contradict `V₁ ≠ K`.
4. Since `S` contains `V₁`, every nonzero field element or its inverse belongs to `S`.
   This also realizes `K` as its fraction field. The characterization in
   [def-trf-valuation-ring] makes `S` a valuation ring, giving the forward implication.
5. Conversely let `U` be a common proper valuation overring and take `t ∉ U`, necessarily
   nonzero. For `u ∈ U`, one has `vᵢ(u) > vᵢ(t)`: otherwise, for nonzero `u`, the element
   `t/u` is in `Vᵢ ⊆ U`, forcing `t ∈ U`. For `u = 0` the inequality follows from infinity.
6. Given a threshold `γ` for valuation `i`, choose nonzero `b` of value
   `γ - vᵢ(t) + εᵢ`. Then `b U` lies in the `i`-ball of threshold `γ`, whereas the `j`-ball
   of threshold `vⱼ(b)` lies in `b Vⱼ ⊆ b U`. Translating gives a `j`-ball inside every
   `i`-ball with the same centre. Interchanging `i` and `j` proves equality of topologies.
-/
theorem topology_eq_iff_exists_common_proper_coarsening
    (K : Type u) [Field K]
    (Γ₁ : Type v) [AddCommGroup Γ₁] [LinearOrder Γ₁] [IsOrderedAddMonoid Γ₁]
    (Γ₂ : Type w) [AddCommGroup Γ₂] [LinearOrder Γ₂] [IsOrderedAddMonoid Γ₂]
    (v₁ : AddValuation K (WithTop Γ₁)) (v₂ : AddValuation K (WithTop Γ₂))
    [v₁.toValuation.IsNontrivial] [v₂.toValuation.IsNontrivial]
    (h₁ : ∀ γ : Γ₁, ∃ x : Kˣ, v₁ (x : K) = (γ : WithTop Γ₁))
    (h₂ : ∀ γ : Γ₂, ∃ x : Kˣ, v₂ (x : K) = (γ : WithTop Γ₂)) :
    v₁.toValuation.subgroups_basis.topology = v₂.toValuation.subgroups_basis.topology ↔
      ∃ U : ValuationSubring K, U ≠ ⊤ ∧
        v₁.toValuation.valuationSubring ≤ U ∧ v₂.toValuation.valuationSubring ≤ U := by
  sorry

end AddValuation
