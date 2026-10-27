module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Algebra.Module.End
import WeilConjectures.Mathlib.Algebra.Lie.Radical
import Sheaf.Algebra.Lie.PerfectLieHyperplaneCriterion
import Mathlib.LinearAlgebra.Trace

/-! # Invariant complements for rational sl₂ operators

Source: Milne, Algebraic Groups (2017), Theorem 23.70, proof (a), printed p.507,
Weyl's semisimplicity input specialized to sl₂ over ℚ
(blueprint: lem-sfb-sl2-invariant-complement).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace RepresentationTheory

/-- A common invariant subspace of three rational endomorphisms satisfying the sl₂
relations has a common invariant complement. `IsCompl U C` means that every vector
has a unique expression as a sum of an element of `U` and an element of `C`.

Source: Milne, Algebraic Groups (2017), Theorem 23.70, proof (a), printed p.507,
with the Casimir argument of Section 22c, pp.475–477
(blueprint: lem-sfb-sl2-invariant-complement).

Proof plan, following the six steps of the DAG node:
1. Let L be the trace-zero rational 2 by 2 matrices, with standard basis e, f, h.
   Their commutators are [h,e] = 2e, [h,f] = -2f, [e,f] = h, so L is perfect.
   For T = ad h, the projectors T(T+2)/8, T(T-2)/8, and 1-T²/4 isolate the e, f, h
   components of an ideal. Any nonzero component generates L by bracketing.
   Thus L is simple and has no nonzero solvable ideal, as in def-wf-lie-algebra
   and def-wf-semisimple-lie-algebra.
2. The given identities define a Lie representation by e ↦ E, f ↦ F, h ↦ H.
   Invariance is exactly stability under the three operators. Apply
   lem-sfb-perfect-lie-hyperplane-criterion: it suffices to split every simple
   invariant hyperplane W in every finite-dimensional rational representation M of L.
3. If its representation r is zero, any linear complement works. Otherwise its
   kernel is a proper ideal of the simple L, so r is injective. Apply
   lem-sfb-faithful-semisimple-trace-form to obtain the nondegenerate form
   B(x,y) = Tr(r(x)r(y)). For a basis xᵢ and its B-dual basis xⁱ, set c = Σᵢ r(xᵢ)r(xⁱ).
4. By lem-pc-finite-dimensional-trace-cyclic, B([z,x],y) + B(x,[z,y]) = 0.
   If [z,xᵢ] = Σⱼ aⱼᵢ xⱼ, duality gives [z,xⁱ] = -Σⱼ aᵢⱼ xʲ. Expanding [r(z),c]
   and exchanging i,j cancels the two sums. Thus c commutes with the action.
   By def-weil-endomorphism-trace and duality, Tr(c) = Σᵢ B(xᵢ,xⁱ) = 3.
5. Perfectness makes the action on the one-dimensional quotient M/W zero.
   Hence r(L)M ⊆ W and c(M) ⊆ W. The trace of a = c restricted to W is 3, so a ≠ 0.
   Its kernel is invariant. Simplicity of W makes that kernel zero, and finite
   dimension makes a invertible. This avoids any algebraic-closure assumption.
6. The map p = a⁻¹c to W is equivariant and restricts to the identity on W.
   Its kernel D is invariant. The expression m = p(m) + (m-p(m)) gives M = W + D,
   and W ∩ D = 0 gives uniqueness. Apply the hyperplane criterion to V and U.
   For U = 0 use C = V; for U = V use C = 0, including V = 0. For the zero
   action every linear complement is invariant.
-/
theorem exists_sl2_invariant_complement
    (V : Type u) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (E F H : Module.End ℚ V)
    (hHE : H * E - E * H = (2 : ℚ) • E)
    (hHF : H * F - F * H = (-2 : ℚ) • F)
    (hEF : E * F - F * E = H)
    (U : Submodule ℚ V)
    (hEU : ∀ v : V, v ∈ U → E v ∈ U)
    (hFU : ∀ v : V, v ∈ U → F v ∈ U)
    (hHU : ∀ v : V, v ∈ U → H v ∈ U) :
    ∃ C : Submodule ℚ V, IsCompl U C ∧
      (∀ v : V, v ∈ C → E v ∈ C) ∧
      (∀ v : V, v ∈ C → F v ∈ C) ∧
      (∀ v : V, v ∈ C → H v ∈ C) := by
  sorry

end RepresentationTheory
