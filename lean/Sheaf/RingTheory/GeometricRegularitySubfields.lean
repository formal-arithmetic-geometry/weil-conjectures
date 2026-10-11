/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.RingTheory.GRing
import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Geometric regularity over a directed union of subfields

Source: Stacks Project, Algebra, Lemma 07QG (blueprint:
lem-weil-pbc-geometrically-regular-over-subfields).
-/

universe u v w

/-- Geometric regularity over a directed union of subfields. Source: Stacks Project,
Algebra, Lemma 07QG (blueprint: lem-weil-pbc-geometrically-regular-over-subfields).

Proof:
1. By def-weil-pbc-g-ring, fix a finite purely inseparable field extension k'/k. Choose a
   finite k-basis of k', giving a surjection from a polynomial algebra to k'. The field k
   is Noetherian (def-weil-pbc-noetherian-ring), and the polynomial algebra is Noetherian
   by lem-weil-pbc-finite-type-algebra-noetherian. Its kernel is finitely generated, so k'
   has a finite presentation by polynomial generators and relations.
2. The relations have finitely many coefficients. By hUnion and hdir, they all lie in
   one K i; use Nonempty I if there are no coefficients. Let k_i' be the quotient of the
   polynomial algebra over K i by these relations.
3. The lemmas lem-weil-pbc-tensor-cancel-base-change,
   lem-weil-pbc-polynomial-scalar-extension, and lem-weil-pbc-tensor-quotient-base-change
   identify k tensor over K i with k_i' with k' as k-algebras. In Stacks' printed identity
   the left side k_i is a misprint for k'.
4. By lem-weil-pbc-finite-purely-inseparable-scalar-descent, k_i' is a field and is finite
   purely inseparable over K i (def-weil-pbc-finite-purely-inseparable-extension).
5. By lem-weil-pbc-tensor-cancel-base-change and symmetry of tensor products, the rings
   k' tensor over k with A and k_i' tensor over K i with A are isomorphic. The latter is
   regular by hgeom and def-weil-pbc-g-ring. Regularity is preserved by ring isomorphisms.
   Since k'/k was arbitrary and A is Noetherian, A is geometrically regular over k.
-/
theorem geometricallyRegular_of_directed_subfields
    (k : Type u) [Field k]
    (I : Type v) [Nonempty I]
    (K : I → Subfield k)
    (hdir : ∀ i j : I, ∃ l : I, K i ≤ K l ∧ K j ≤ K l)
    (hUnion : ∀ x : k, ∃ i : I, x ∈ K i)
    (A : Type w) [CommRing A] [Algebra k A]
    (hA : IsNoetherianRing A)
    (hgeom : ∀ i : I, Algebra.IsGeometricallyRegular (K i) A) :
    Algebra.IsGeometricallyRegular k A := by
  sorry
