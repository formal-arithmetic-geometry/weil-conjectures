module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.Fintype.Perm

/-! # Rigidity of a finite loopless multigraph from its integral cycles

Source: Deligne–Mumford, The irreducibility of the space of curves of given genus,
the graph argument following Lemma 1.17, printed pp. 86–87
(blueprint: lem-sfb-finite-graph-homology-rigidity).

An orientation is specified by source and target maps `s` and `t`. Distinct edge
indices may have the same endpoints. All operators below are the linear extensions
of their displayed values on the standard integral basis, so no arbitrary choice of
an action on homology is involved.
-/

@[expose] public section

set_option autoImplicit false

universe u v

/-- The integral cycle lattice is free of finite rank, and an automorphism fixing
all vertices of degree at most two and every integral cycle fixes every vertex and edge.

Source: Deligne–Mumford, graph argument after Lemma 1.17, printed pp. 86–87
(blueprint: lem-sfb-finite-graph-homology-rigidity).

Proof: Apply `Submodule.basisOfPid` to the kernel in the finite free edge module
([lem-weil-subgroup-finite-free-abelian-group-free]) for the first clause.
For rigidity, induct strongly on the sum of the vertex and edge cardinalities.
Changing orientations conjugates the boundary and signed action and preserves the
hypotheses. The empty graph is immediate. Delete an isolated vertex, which is fixed.
For a degree-one vertex, its incident edge and its neighbour are fixed; delete the
vertex and edge. A cycle has zero coefficient on that edge, giving the equivariant
identification of cycle kernels, and only the already fixed neighbour loses degree.
For a fixed degree-two vertex whose two edges have the same other endpoint, that
endpoint is fixed. Swapping these edges negates their nonzero difference cycle,
so both edges are fixed. Delete the vertex and its two edges, embedding the remaining
cycles by zero extension; only the fixed other endpoint changes degree.
For a degree-two vertex with distinct neighbours, suppress the two-edge path to one
edge. The boundary at the vertex forces its two oriented coefficients to agree,
so suppression identifies cycle kernels equivariantly, including the negative sign
if the neighbours are interchanged. Degrees of retained vertices are unchanged.
Induction fixes the reduced graph, hence the original two edges as well.
Now all degrees are at least three. If an edge and both its endpoints are fixed,
delete that edge. Zero extension embeds the remaining cycle lattice equivariantly,
and only already fixed vertices lose degree, so induction applies again.
Otherwise there are no fixed edges with fixed endpoints. By
[lem-sfb-finite-graph-euler-trace], put `b = |E| - |V| + c`, where `c` counts components.
Clearing denominators extends identity on integral cycles to rational cycles, whose
trace is `b`. The degree bound gives `2|E| ≥ 3|V|`, hence `b > c` when vertices exist.
The trace formula gives `0 ≤ f₀ + f₋ = f_c - b ≤ c - b < 0`, a contradiction.
Empty vertices force empty edges by looplessness. No connectedness is used. -/
theorem finiteGraphHomologyRigidity
    (V : Type u) (E : Type v) [Finite V] [Fintype E] [DecidableEq V]
    (s t : E → V) (_hne : ∀ e : E, s e ≠ t e) :
    (∃ r : ℕ, Nonempty (Module.Basis (Fin r) ℤ
      (LinearMap.ker (Finsupp.linearCombination ℤ
        (fun e : E ↦ Finsupp.single (t e) (1 : ℤ) - Finsupp.single (s e) 1))))) ∧
    ∀ (σV : Equiv.Perm V) (σE : Equiv.Perm E),
      (∀ e : E,
        (σV (s e) = s (σE e) ∧ σV (t e) = t (σE e)) ∨
        (σV (s e) = t (σE e) ∧ σV (t e) = s (σE e))) →
      (∀ x : V, (Finset.univ.filter (fun e : E ↦ s e = x ∨ t e = x)).card ≤ 2 →
        σV x = x) →
      (∀ c : E →₀ ℤ,
        Finsupp.linearCombination ℤ
          (fun e : E ↦ Finsupp.single (t e) (1 : ℤ) - Finsupp.single (s e) 1) c = 0 →
        Finsupp.linearCombination ℤ
          (fun e : E ↦ if σV (s e) = s (σE e)
            then Finsupp.single (σE e) (1 : ℤ)
            else -Finsupp.single (σE e) 1) c = c) →
      σV = Equiv.refl V ∧ σE = Equiv.refl E := by
  sorry
