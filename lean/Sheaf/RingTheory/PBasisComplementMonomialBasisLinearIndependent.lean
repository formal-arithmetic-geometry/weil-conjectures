module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Algebra.ZMod


@[expose] public section
set_option autoImplicit false
universe u w
attribute [local instance] ZMod.algebra
namespace RingTheory

/-- Independence over the complementary p-basis subfield.
Source: Stacks Project, Tag 07P5, first proof paragraph, expanded by the
bounded-monomial argument of the parent node.
(blueprint: lem-weil-pbc-p-basis-complement-monomial-basis-linearIndependent).

Proof: Frobenius has subfield image F, containing the prime field; hence this
image equals F_p(k^p). Let L be the F-span of bounded complementary monomials.
It contains 1 and the complementary generators. Multiplication preserves L by
reducing exponents modulo p and absorbing p-th powers into F. If a is nonzero
in L, a^p lies in F, and a inverse = (a^p) inverse times a^(p-1) lies in L.
Thus L is a subfield, and the generating property identifies it with kJ.
In any finite kJ-linear relation among the J monomials, expand each coefficient
as a finite F-linear combination of bounded complementary monomials. Pairing
J exponents with complementary exponents is injective: the restrictions recover
each member of the pair. The original F-basis is linearly independent, so all
expanded coordinates vanish. Every original coefficient is zero. This proves
independence, including empty J, when the family consists of the single nonzero
monomial 1. -/
theorem pBasisComplementMonomialBasis_linearIndependent
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
    LinearIndependent kJ (fun E : J → Fin p ↦ ∏ i : J, t i ^ (E i : ℕ)) := by
  sorry

end RingTheory
