/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSortingOperators

/-!
# Unsigned correspondence for tail deletions

Source: Stacks Project, Tag 01FM, verification of equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-tail-deletion-correspondence)
-/

@[expose] public section

set_option autoImplicit false

universe v

namespace AlgebraicGeometry.Scheme

/-- Filtered outgoing tail indices, retaining original labels.
Source: Stacks 01FM, equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-tail-deletion-correspondence) -/
abbrev cechTailOutgoingIndex {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :=
  {x : Equiv.Perm (Fin (p + 2)) × Fin (p + 2) ×
      Equiv.Perm (Fin (p + 2)) × Fin (p + 3) //
    ((cechStableSort t x.1 ∧ cechPartialSort x.1 x.2.2.1 x.2.1) ∧
      cechJunction x.1 x.2.2.1 x.2.1 x.2.2.2 ≠ x.1 x.2.1) ∧
      ¬ x.2.2.2.val < x.2.1.val}

/-- Filtered incoming indices whose omitted label follows the junction in stable order.
Source: Stacks 01FM, equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-tail-deletion-correspondence) -/
abbrev cechTailIncomingIndex {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :=
  {y : Fin (p + 2) × Equiv.Perm (Fin (p + 1)) × Fin (p + 1) ×
      Equiv.Perm (Fin (p + 1)) //
    (cechStableSort (t ∘ y.1.succAbove) y.2.1 ∧
      cechPartialSort y.2.1 y.2.2.2 y.2.2.1) ∧
      ¬ (t y.1 < t (y.1.succAbove (y.2.1 y.2.2.1)) ∨
        (t y.1 = t (y.1.succAbove (y.2.1 y.2.2.1)) ∧
          y.1 < y.1.succAbove (y.2.1 y.2.2.1)))}

/-- Tail deletion gives a bijection of the filtered index sets, preserving junction
maps and identifying the incoming partial permutation with the deleted outgoing one.
No signs, coefficients, abelian groups, or sums enter this assertion.

Source: Stacks 01FM, omitted verification of equation 20.23.6.1; the unsigned
labelled-deletion part of the proof of the tail cancellation lemma.

Proof: Give original labels the strict lexicographic order (t i, i). Stable sorts
are unique in this order, and partial sorts are unique because their prefix is fixed
and their complementary labels form an increasing tail. For an outgoing index
(σ,a,τ,r), the nonjunction condition rules out r=a. Thus r>a and k=r-1 is a valid
position in τ. Put j=τ k. The tail is disjoint from the sorted prefix; j also differs
from σ a, so its stable rank is strictly after a. Delete j from σ and from τ, using
j.succAbove to renumber the remaining original labels. In σ remove its stable rank;
in τ remove k. This gives the incoming stable sort ρ and partial sort η, with b=a.
The omitted label follows the surviving junction in lexicographic order. On each
surviving position the restriction of τ is j.succAbove ∘ η. For the junction map,
positions at most a are in the unchanged sorted prefix, and positions after a use
that same restricted tail; this proves the asserted equality of maps.

Conversely, from (j,ρ,b,η), insert j into the stable sort of the remaining labels
at its lexicographic rank, which is strictly greater than b since j is not before
the junction and cannot equal its distinct original label. Insert j into the
increasing complementary tail of η at its original-label rank k, leaving the
prefix of length b fixed. Set a=b and r=k+1. Then r>a, τ k=j differs from the
junction, and the outgoing filter holds. Restriction and insertion are inverse:
the sorted prefix is unchanged, and both orders uniquely determine the inserted
positions. This proves bijectivity and all displayed identities. For the last
prefix a=p+1 the outgoing filter is empty: only the junction label remains in
the tail. For p=0 this is the same construction on two labels and one surviving
label. Equal t-values are distinguished by their original labels, and for an
empty I there is no tuple t.
(blueprint: lem-pc-alternating-cech-tail-deletion-correspondence) -/
theorem cechTailDeletionCorrespondence {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :
    ∃ e : cechTailOutgoingIndex p t ≃ cechTailIncomingIndex p t,
      ∀ x, ∃ k : Fin (p + 2),
        k.val + 1 = x.val.2.2.2.val ∧
        x.val.2.2.1 k = (e x).val.1 ∧
        (∀ z, x.val.2.2.1 (k.succAbove z) =
          (e x).val.1.succAbove ((e x).val.2.2.2 z)) ∧
        x.val.2.1.val = (e x).val.2.2.1.val ∧
        cechJunction x.val.1 x.val.2.2.1 x.val.2.1 ∘ x.val.2.2.2.succAbove =
          (e x).val.1.succAbove ∘
            cechJunction (e x).val.2.1 (e x).val.2.2.2 (e x).val.2.2.1 := by sorry

end AlgebraicGeometry.Scheme
