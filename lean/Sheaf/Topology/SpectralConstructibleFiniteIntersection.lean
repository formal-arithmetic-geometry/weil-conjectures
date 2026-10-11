module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Spectral.Basic

/-!
# Finite intersections of constructible subsets of a spectral space

Source: literature/stacks-project/topology.tex, Topology, Lemma 0901 and the
paragraph before it (blueprint: lem-weil-pbc-spectral-constructible-finite-intersection).

## Main statements

- `finite_subfamily_iInter_eq_empty_of_isConstructible`: a family of constructible
  subsets with empty intersection has a finite subfamily with empty intersection.
-/

@[expose] public section

universe u v

open Set Topology

/-- In a spectral space, a family of constructible subsets with empty intersection
has a finite subfamily with empty intersection.

Source: literature/stacks-project/topology.tex, Topology, Lemma 0901 and the
paragraph before it (blueprint: lem-weil-pbc-spectral-constructible-finite-intersection).
Proof: Put the constructible topology on the spectral space. Constructible sets
are closed there, and that topology is quasi-compact. The complements therefore
form an open cover, which has a finite subcover; taking complements gives the
finite subfamily. The empty space is handled by the empty finite subfamily.
-/
theorem finite_subfamily_iInter_eq_empty_of_isConstructible
    (T : Type u) [TopologicalSpace T] [SpectralSpace T]
    (A : Type v) (E : A → Set T)
    (hE : ∀ a, IsConstructible (E a))
    (hEmpty : (⋂ a, E a) = ∅) :
    ∃ A₀ : Finset A, (⋂ a ∈ A₀, E a) = ∅ := by
  sorry
