module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Algebra.ZMod

@[expose] public section
set_option autoImplicit false
universe u w
attribute [local instance] ZMod.algebra
namespace RingTheory

/-- Spanning over the complementary p-basis subfield.
Source: Stacks Project, Tag 07P5, first proof paragraph, expanded by the
bounded-monomial argument of the parent node.
(blueprint: lem-weil-pbc-p-basis-complement-monomial-basis-spanning).

Proof: Put F = F_p(k^p). All elements of F lie in kJ since the latter contains
p-th powers and the prime field. Expand x in the given F-basis, with finitely
many nonzero coordinates. Split each bounded exponent function into its restriction
to J and to I minus J. The complementary monomial belongs to kJ, since each
of its generators lies there. Its product with the original F-coordinate is
therefore a kJ coefficient. Group the finitely many terms by their restriction
to J. This expresses x in the kJ-span of the displayed J monomials. For empty
J this also shows kJ = k, and the only displayed monomial is 1.
-/
theorem pBasisComplementMonomialBasis_spanning
    (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    (I : Type w) (t : I → k)
    (hpb : ∃ b : Module.Basis
      {E : I →₀ ℕ // ∀ i : I, E i < p}
      (IntermediateField.adjoin (ZMod p) (Set.range (fun x : k ↦ x ^ p))) k,
      ∀ E, b E = (E : I →₀ ℕ).prod (fun i e ↦ t i ^ e))
    (J : Finset I) (kJ : Subfield k)
    (hkJ : kJ = Subfield.closure
      (Set.range (fun x : k ↦ x ^ p) ∪ {x : k | ∃ i : I, i ∉ J ∧ t i = x})) :
    ⊤ ≤ Submodule.span kJ (Set.range (fun E : J → Fin p ↦ ∏ i : J, t i ^ (E i : ℕ))) := by
  sorry

end RingTheory
