module

public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.Metrizable.Basic

/-!
# A profinite cover with countably many dense double fibres

Source: the agent-formulated topology auxiliary in the DAG node below, associated with
literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3).
The blueprint itself does not state this auxiliary; an external reference is wanted.
(blueprint: lem-sfb-countable-split-profinite-cover)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Profinite

/-- There exists a metrizable profinite cover with countably many double fibres, whose
ordered off-diagonal pairs are clopen in its relation space and whose double fibres
lie arbitrarily far along the enumeration inside every nonempty open set.

Source: the agent-formulated pure-topology auxiliary associated with paragraph (3) of
the blueprint open-direct-image proof, with complete construction in the DAG node
(blueprint: lem-sfb-countable-split-profinite-cover). This is not a theorem of the
blueprint itself; an external reference remains wanted.

Proof in words: take Cantor space V with its lexicographic order, embedded continuously
and injectively in the real Cantor set. Enumerate without repetitions the countable
set D of sequences eventually equal to the periodic sequence 0101..., so every cylinder
contains infinitely many enumerated points. No such point is eventually constant; it
is approached from either side by points outside D. Set a_k = 2^(-k-3). On V minus D
sum the step functions taking values -a_k below v_k and a_k above it. The series is
uniformly convergent. It is continuous away from D; at v_k its two one-sided limits
are g_k - a_k and g_k + a_k, where g_k sums all the other summands.

Let T be the graph closure in V times [-1/4,1/4], and q its first projection. Compactness
and density of V minus D imply surjectivity. The preceding limit calculation gives
exactly the stated singleton and double fibres. T is compact Hausdorff and metrizable.
Every connected subset projects to a singleton in V and hence lies in a finite fibre;
it is therefore a singleton, proving total disconnectedness.

In the relation space, use disjoint height intervals of radius a_k/2 about g_k - a_k
and g_k + a_k. Any pair in their product has height gap strictly between a_k and 3a_k.
An off-diagonal pair over v_j has gap 2a_j; the dyadic amplitudes force j = k.
This isolates each ordered pair, and Hausdorffness makes its singleton closed.
Finally a nonempty open U meets the dense graph at a singleton fibre over x. The
complement of q(T minus U) is an open neighbourhood of x all of whose fibres lie in U.
Every tail of the enumeration meets this neighbourhood, yielding the last assertion.
The universe convention is `def-weil-size-convention`, represented by the explicit u.
-/
theorem exists_countable_split_profinite_cover :
    ∃ (T V : Profinite.{u}),
      Nonempty T ∧ Nonempty V ∧
      TopologicalSpace.MetrizableSpace T ∧ TopologicalSpace.MetrizableSpace V ∧
      ∃ (q : C(T, V)), Function.Surjective q ∧
        ∃ (v : ℕ → V) (tMinus tPlus : ℕ → T),
          Function.Injective v ∧
          (∀ k : ℕ, tMinus k ≠ tPlus k ∧
            q ⁻¹' {v k} = {tMinus k, tPlus k}) ∧
          (∀ y : V, y ∉ Set.range v → ∃! x : T, q x = y) ∧
          (∀ k : ℕ,
            IsClopen {r : {p : T × T // q p.1 = q p.2} |
              r.val = (tMinus k, tPlus k)} ∧
            IsClopen {r : {p : T × T // q p.1 = q p.2} |
              r.val = (tPlus k, tMinus k)}) ∧
          (∀ U : Set T, IsOpen U → U.Nonempty → ∀ N : ℕ,
            ∃ k : ℕ, N ≤ k ∧ tMinus k ∈ U ∧ tPlus k ∈ U) := by
  sorry

end Profinite
