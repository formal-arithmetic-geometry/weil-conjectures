module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Homeomorph.Defs

/-! # Continuous sections obtained by lifting a finite topological basis

Source: the Weil conjectures blueprint, `sec-six-functors-basics`,
`sk-lem-stratified-lattice`, proof, “Pushing down by the trace”, continuous lifting
through the sum map (blueprint: lem-sfb-topological-basis-lift-section).
-/

@[expose] public section

universe u v w t z z'

namespace Module.Basis

/-- Lifting a finite basis with homeomorphic coordinates gives a continuous linear section,
including the induced split surjection on continuous function modules and its naturality.
Source: the Weil conjectures blueprint, `sk-lem-stratified-lattice`, proof,
“Pushing down by the trace” (blueprint: lem-sfb-topological-basis-lift-section).

Proof plan:
1. The inverse coordinates of the basis are linear by uniqueness of basis expansions
   (`def-weil-pbc-free-module`); on a basis vector they are the corresponding unit vector.
2. For any prescribed lifts `m`, define `s x` as the finite sum of the coordinates of `x`
   times `m i`. Distributivity and linearity of coordinates give linearity of this formula.
3. Applying `q` to the sum replaces each `m i` by `b i`, giving `x`. Unit-vector coordinates
   give `s (b i) = m i`.
4. The coordinates are continuous by the homeomorphism assumption. Each summand is continuous
   by the continuous scalar action, and finite sums are continuous by continuous addition.
5. Surjectivity of `q` supplies the lifts and hence existence of a section. For an empty basis
   the target is zero and the sum is empty, so the section is the zero map.
6. Continuous scalar functions act pointwise on continuous module-valued functions: pairing
   continuous functions and composing with the assumed operations proves continuity; the
   ring and module identities hold pointwise.
7. Postcomposition with `q` and `s` preserves continuity and is linear over the continuous
   scalar functions, as is checked at each point. The section identity holds pointwise and
   makes postcomposition with `q` surjective, including for an empty source space.
8. Associativity of composition proves that both postcomposition maps commute with
   precomposition by every continuous map, with scalars restricted by the same precomposition.
The coordinate calculations also apply to the zero ring and the zero module. -/
theorem exists_continuousLinearMap_section_of_isHomeomorph_equivFun_symm
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul A M]
    {N : Type w} [AddCommGroup N] [Module A N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [ContinuousSMul A N]
    {I : Type t} [Fintype I] (b : Module.Basis I A N)
    (hβ : IsHomeomorph (b.equivFun.symm : (I → A) → N))
    (q : M →L[A] N) (hq : Function.Surjective q) :
    (∃ s : N →L[A] M, Function.RightInverse s q) ∧
    ∀ (m : I → M), (∀ i : I, q (m i) = b i) →
      ∃ s : N →L[A] M,
        (∀ x : N, s x = ∑ i : I, b.equivFun x i • m i) ∧
        Function.RightInverse s q ∧ (∀ i : I, s (b i) = m i) ∧
        ∀ (Z : Type z) [TopologicalSpace Z],
          ∃ (Q : C(Z, M) →ₗ[C(Z, A)] C(Z, N))
            (S : C(Z, N) →ₗ[C(Z, A)] C(Z, M)),
            (∀ f : C(Z, M), Q f = (ContinuousMap.mk q q.continuous).comp f) ∧
            (∀ f : C(Z, N), S f = (ContinuousMap.mk s s.continuous).comp f) ∧
            Function.Surjective Q ∧ Function.RightInverse S Q ∧
            ∀ (Z' : Type z') [TopologicalSpace Z'] (a : C(Z', Z)),
              (∀ f : C(Z, M),
                (ContinuousMap.mk q q.continuous).comp (f.comp a) = (Q f).comp a) ∧
              (∀ f : C(Z, N),
                (ContinuousMap.mk s s.continuous).comp (f.comp a) = (S f).comp a) := by
  sorry

end Module.Basis
