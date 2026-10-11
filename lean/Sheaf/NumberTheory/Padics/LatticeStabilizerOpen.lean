/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.NumberTheory.Padics.CoefficientExtension
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.CompactOpen
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Openness of a p-adic lattice stabilizer

Source: Stanford Weil II seminar, Lecture 19, Proposition 1.1.9, second bullet
(blueprint: lem-pod-lattice-stabilizer-open).
- The topology on the coefficient field is its spectral norm topology.
- The topology on the automorphisms is induced from compact-open continuous maps.
-/

universe u v

namespace Padic

/-- The stabilizer of a finitely generated spanning lattice is open.

Source: Stanford Weil II seminar, Lecture 19, Proposition 1.1.9, second bullet
(blueprint: lem-pod-lattice-stabilizer-open).

Proof: By `lem-sc-dvr-fg-torsionfree-free`, the lattice is free over the DVR supplied by
`def-weil-l-adic-coefficient-extension`. A lattice basis is an E-basis because the lattice
spans V. In that basis, preservation of the lattice is equivalent to both the matrix and
its inverse having entries in the valuation ring. For a stabilizing matrix A, every matrix
A+B with B in M_n(m_E) is invertible over the valuation ring: factor it as A(I+A⁻¹B), whose
second factor has determinant congruent to 1 modulo m_E, and use the adjugate formula.
Evaluation at a basis vector is continuous for the compact-open topology, and basis
coordinates are continuous for the specified product topology. Since m_E is the open
absolute-value ball of radius 1, the finitely many entry conditions defining A+M_n(m_E)
give an open neighborhood of A inside the stabilizer. Thus the stabilizer is open.

The coordinate hypothesis says that a basis coordinate equivalence is a homeomorphism onto
the finite product. All linear automorphisms are then continuous, so continuous linear
automorphisms represent the full GL_E(V). Their topology is explicitly induced from C(V,V),
whose Mathlib topology is compact-open, rather than from operator-norm continuous maps. -/
theorem lattice_stabilizer_isOpen (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    letI : NormedField E := spectralNorm.normedField ℚ_[l] E
    ∀ (V : Type v) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      [TopologicalSpace V],
      (∃ b : Module.Basis (Fin (Module.finrank E V)) E V,
        Continuous b.equivFun ∧ Continuous b.equivFun.symm) →
      ∀ (Λ : Submodule (coefficientExtensionIntegers l E) V),
        Λ.FG → Submodule.span E (Λ : Set V) = ⊤ →
        letI : TopologicalSpace (V ≃L[E] V) :=
          TopologicalSpace.induced (fun g : V ≃L[E] V ↦ (g : C(V, V))) inferInstance
        IsOpen {g : V ≃L[E] V | g '' (Λ : Set V) = (Λ : Set V)} := by
  sorry

end Padic
