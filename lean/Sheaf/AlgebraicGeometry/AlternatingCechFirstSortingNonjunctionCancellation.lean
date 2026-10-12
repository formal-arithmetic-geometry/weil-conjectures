/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSortingOperators

/-!
# Nonjunction cancellation in the first sorting homotopy

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-first-sorting-nonjunction-cancellation)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

open Classical in
/-- Outgoing nonjunction deletions cancel the incoming differential expansion.

Source: Stacks 01FM, verification of equation 20.23.6.1 (the computation omitted
in the source), nonjunction terms of the labelled-deletion argument.

Proof: A stable permutation exists uniquely by ordering the finite set of labels
by (value, original position). For every prefix length, the partial permutation
exists uniquely by keeping that prefix and enumerating the unused labels
in their original increasing order. Thus both permutation filters pick one term.
Label the entries of t by their original positions. An outgoing deletion
r whose junction label j differs from σ a removes a label occurring only once.
If r<a, delete j from the sorted prefix and use prefix length a-1 on the face
of t omitting j; if r>a, remove j from the increasing tail and keep prefix
length a. Restrict σ to the remaining original labels, renumbered increasingly;
it is the stable sort of that face. Restrict τ in the same way; its prefix is
fixed and its unused tail is increasing. Conversely each term of the incoming
face differential and its junction homotopy inserts j in the stable sorted
position: before the junction if j precedes its sorted label, and otherwise in
the increasing tail. These operations are inverse and partition the terms.
For a prefix deletion r<a, j=τ r and the restricted permutation has sign
(-1)^(r+j) sign τ. Its incoming prefix length is a-1, giving coefficient
(-1)^(j+a-1+r+j) sign τ = -(-1)^(a+r) sign τ.
For a tail deletion r>a, j=τ (r-1) and the restricted permutation has sign
(-1)^(r-1+j) sign τ. Its incoming prefix length is a, giving coefficient
(-1)^(j+a+r-1+j) sign τ = -(-1)^(a+r) sign τ.
The sign restriction formula follows by moving the removed position and its
label to the end, then restricting the permutation. The index-map composites have
identical projections onto every remaining entry, so uniqueness in the product
universal property identifies them. Restriction of sections and the integer
multiples therefore cancel in pairs. Stable sorting of labelled pairs also proves
this for repeated values.
The smallest degree and the empty index type require no excluded hypothesis.
(blueprint: lem-pc-alternating-cech-first-sorting-nonjunction-cancellation) -/
theorem cechFirstSortingNonjunctionCancellation (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (s : S.cochains F (p + 1)) (t : Fin (p + 2) → I) :
    let E := fun (σ : Equiv.Perm (Fin (p + 2))) (a : Fin (p + 2))
        (τ : Equiv.Perm (Fin (p + 2))) (r : Fin (p + 3)) ↦
      ((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) •
        F.map (S.indexMap t (cechJunction σ τ a)).op
          ((-1 : ℤ) ^ r.val •
            F.map (S.indexMap (t ∘ cechJunction σ τ a) r.succAbove).op
              (s ((t ∘ cechJunction σ τ a) ∘ r.succAbove)))
    (∑ σ : Equiv.Perm (Fin (p + 2)), ∑ a : Fin (p + 2),
      ∑ τ : Equiv.Perm (Fin (p + 2)), ∑ r : Fin (p + 3),
        if (cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
            cechJunction σ τ a r ≠ σ a then E σ a τ r else 0) +
      (S.differential F p (cechFirstSortingHom X U F S p s)) t = 0 := by sorry

end AlgebraicGeometry.Scheme
