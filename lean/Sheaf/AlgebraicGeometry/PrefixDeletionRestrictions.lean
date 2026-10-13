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

/-- Restriction identities for a prefix-deletion equivalence satisfying its base facts.
Source: Stacks Project, Tag 01FM, prefix-deletion correspondence.
Proof: Fix an outgoing x=(σ,a,τ,r) and put e(x)=(j,ρ,b,η).
The hypothesis gives a=b+1, r<n=p+2 and τ(r)=j. Since r<a,
prefix agreement also gives σ(r)=j. Delete position r and label j from σ and τ,
renumbering through the increasing bijections r.succAbove and j.succAbove.
Call the resulting permutations ρ₀ and η₀. Restriction gives genuine
permutations because σ and τ send the deleted position to the deleted label.
Stable sorting of σ restricts to stable sorting of ρ₀ for t∘j.succAbove:
monotonicity is preserved by increasing position renumbering, and equal values
are ordered by increasing label renumbering. Any stable permutation of a finite
tuple is unique: it enumerates its distinct pairs (value,original label) in
strict lexicographic order. Since ρ is also stable for this tuple, ρ₀=ρ.
For k<b, r.succAbove(k)<a, so η₀(k)=ρ₀(k). For b≤k<l,
a≤r.succAbove(k)<r.succAbove(l); increasing tails of τ and j.succAbove
then give η₀(k)<η₀(l). Thus η₀ is partial sorted with prefix b and stable
permutation ρ. Such a partial sorting is unique: the prefix prescribes its
labels, and the tail must enumerate the remaining labels in increasing order.
The incoming property gives the same constraints on η, hence η₀=η.
The defining restriction equations now give the two asserted identities.
This proof is pointwise and needs no particular construction of e, nor its
bijectivity or the before condition. It includes p=0, b=0, b=p and repeated
values. For an empty I there are no tuples to check.
(blueprint: new-prefix-deletion-restrictions) -/
theorem prefixDeletionRestrictions {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I)
    (e : ({x : Equiv.Perm (Fin (p + 2)) × Fin (p + 2) ×
      Equiv.Perm (Fin (p + 2)) × Fin (p + 3) //
    (cechStableSort t x.1 ∧ cechPartialSort x.1 x.2.2.1 x.2.1) ∧
      x.2.2.2.val < x.2.1.val}) ≃
      ({y : Fin (p + 2) × Equiv.Perm (Fin (p + 1)) × Fin (p + 1) ×
      Equiv.Perm (Fin (p + 1)) //
    (cechStableSort (t ∘ y.1.succAbove) y.2.1 ∧
      cechPartialSort y.2.1 y.2.2.2 y.2.2.1) ∧
    (t y.1 < t (y.1.succAbove (y.2.1 y.2.2.1)) ∨
      (t y.1 = t (y.1.succAbove (y.2.1 y.2.2.1)) ∧
        y.1 < y.1.succAbove (y.2.1 y.2.2.1)))}))
    (h : ∀ x, let y := e x
      x.1.2.1.val = y.1.2.2.1.val + 1 ∧
      ∃ hr : x.1.2.2.2.val < p + 2,
        x.1.2.2.1 ⟨x.1.2.2.2.val, hr⟩ = y.1.1) :
    ∀ x,
      let y := e x
      ∃ hr : x.1.2.2.2.val < p + 2,
        (∀ k : Fin (p + 1),
          x.1.1 ((⟨x.1.2.2.2.val, hr⟩ : Fin (p + 2)).succAbove k) =
            y.1.1.succAbove (y.1.2.1 k)) ∧
        (∀ k : Fin (p + 1),
          x.1.2.2.1 ((⟨x.1.2.2.2.val, hr⟩ : Fin (p + 2)).succAbove k) =
            y.1.1.succAbove (y.1.2.2.2 k)) := by sorry

end AlgebraicGeometry.Scheme
