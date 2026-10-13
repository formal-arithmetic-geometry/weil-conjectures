/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSortingOperators

@[expose] public section
set_option autoImplicit false
universe v
namespace AlgebraicGeometry.Scheme

/-- Existence of the prefix-deletion equivalence, with its index and junction facts.
Source: Stacks Project, Tag 01FM, prefix-deletion correspondence.
Proof: Write n=p+2. For an outgoing (σ,a,τ,r), the inequality r<a<n
makes r a position of both permutations and forces a≥1. Prefix agreement gives
j=σ(r)=τ(r). Restrict σ and τ to the complements of position r and label j,
using the increasing bijections r.succAbove and j.succAbove to renumber them,
and put b=a-1. The resulting permutations ρ and η are genuine bijections:
σ and τ restrict to bijections of these complements. Increasing renumbering
preserves the stable order of the pairs (t(k),k), hence ρ is stably sorted.
For k<b, r.succAbove(k)<a, so the two restricted prefixes agree. For b≤k<l,
a≤r.succAbove(k)<r.succAbove(l); thus the restricted tail of η increases.
The entry of ρ at b came from position a of σ. Since r<a, its pair follows
(t(j),j), giving exactly the incoming before condition.
Conversely, for incoming (j,ρ,b,η), let r be the number of labels whose pair
(t(k),k) precedes (t(j),j). The before condition says r≤b. Insert j at position r
into both permutations j.succAbove∘ρ and j.succAbove∘η, and put a=b+1<n.
The first permutation is stably sorted. Before a, the second agrees with it:
the inserted position agrees, and the other positions correspond to k<b.
Starting at a, positions correspond to k≥b, so the second tail increases.
These are permutations because insertion restores exactly the missing label.
Deletion followed by insertion restores the original permutations because the
stable order fixes the unique rank r; insertion followed by deletion restores
the two smaller permutations. The prefix lengths also recover each other.
Thus the maps are inverse and define the required equivalence. By construction
a=b+1 and τ(r)=j. For p=0 the smaller permutations are identities; the argument
also includes b=0 and b=p. Equal t-values use the original label as tie breaker;
an empty I admits no input tuple.
(blueprint: new-prefix-deletion-existence) -/
theorem prefixDeletionExistence {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :
    ∃ e : ({x : Equiv.Perm (Fin (p + 2)) × Fin (p + 2) ×
      Equiv.Perm (Fin (p + 2)) × Fin (p + 3) //
    (cechStableSort t x.1 ∧ cechPartialSort x.1 x.2.2.1 x.2.1) ∧
      x.2.2.2.val < x.2.1.val}) ≃
      ({y : Fin (p + 2) × Equiv.Perm (Fin (p + 1)) × Fin (p + 1) ×
      Equiv.Perm (Fin (p + 1)) //
    (cechStableSort (t ∘ y.1.succAbove) y.2.1 ∧
      cechPartialSort y.2.1 y.2.2.2 y.2.2.1) ∧
    (t y.1 < t (y.1.succAbove (y.2.1 y.2.2.1)) ∨
      (t y.1 = t (y.1.succAbove (y.2.1 y.2.2.1)) ∧
        y.1 < y.1.succAbove (y.2.1 y.2.2.1)))}), ∀ x,
      let y := e x
      x.1.2.1.val = y.1.2.2.1.val + 1 ∧
      ∃ hr : x.1.2.2.2.val < p + 2,
        x.1.2.2.1 ⟨x.1.2.2.2.val, hr⟩ = y.1.1 := by sorry

end AlgebraicGeometry.Scheme
