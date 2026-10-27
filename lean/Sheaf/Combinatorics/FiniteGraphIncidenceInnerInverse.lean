module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.StdBasis

/-! # Integral inner inverse of a finite graph incidence map

Source: literature/stacks-project/curves.tex, agent-written integral-lattice auxiliary for
Tag 0C1M, lemma-glue-points, units-sequence proof.
(blueprint: lem-sfb-finite-graph-incidence-inner-inverse).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace FiniteGraphCycleCharacter

/-- The incidence map of a finite loopless directed multigraph has an integral inner inverse.

Source: literature/stacks-project/curves.tex, agent-written integral-lattice auxiliary for
Tag 0C1M, lemma-glue-points, units-sequence proof, which motivates but does not assert this lemma.
(blueprint: lem-sfb-finite-graph-incidence-inner-inverse).

Proof: (1) Relate vertices u and v when some integral edge vector has boundary b_v - b_u.
Zero, negation, and addition prove reflexivity, symmetry, and transitivity. The standard
vector of an edge relates its source and target.
(2) Choose one representative a_C for each equivalence class C. For each vertex v in C,
choose an edge vector p_v with boundary b_v - b_a_C, as supplied by the relation. Both
endpoints of an edge have the same representative. No choice is required if V is empty.
(3) Define r(x) as the finite sum of x(v) times p_v. Distributivity makes r integral-linear,
and the standard-basis expansion [def-weil-pbc-free-module] gives r(b_v) = p_v.
(4) On an edge basis vector, boundary r boundary is
(b_target - b_a_C) - (b_source - b_a_C) = b_target - b_source.
Linearity and the standard-basis expansion [def-weil-pbc-free-module] extend this identity
to every edge vector, including the empty sum when E is empty. -/
theorem exists_incidence_innerInverse {V : Type u} {E : Type v} [Finite V] [Finite E]
    (s t : E → V) (_hne : ∀ e : E, s e ≠ t e)
    (d : (E → ℤ) →ₗ[ℤ] (V → ℤ))
    (hd : ∀ e : E, d ((Pi.basisFun ℤ E) e) =
      (Pi.basisFun ℤ V) (t e) - (Pi.basisFun ℤ V) (s e)) :
    ∃ r : (V → ℤ) →ₗ[ℤ] (E → ℤ), d ∘ₗ r ∘ₗ d = d := by
  sorry

end FiniteGraphCycleCharacter
