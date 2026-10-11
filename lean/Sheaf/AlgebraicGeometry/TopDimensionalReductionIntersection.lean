/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.AlgebraicGeometry.IntersectionNumber
import WeilConjectures.AlgebraicGeometry.Modules.Ample
import Mathlib.RingTheory.Length
import Mathlib.Topology.Sober

/-! # Reduction of intersection numbers to top-dimensional components

Source: Stacks Project, Varieties, Lemma 33.45.6, Tag 0BES, used in Tag 0BEV
(blueprint: lem-sc-top-dimensional-reduction-intersection).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Intersection numbers are the sum of their top-dimensional component contributions,
weighted by the positive generic lengths. `components` lists each top-dimensional component
exactly once. The integral closed immersions `c` give the reduced induced structures on these
components. Their dimension equalities `hY` also follow from `hc` and the closed embeddings;
they are explicit to supply the dimension proofs required by `intersectionNumber`.
The natural numbers `m` are identified with the actual lengths in `ℕ∞`, so their finiteness
is asserted rather than assumed. The last clause gives the ample self-intersection consequence.

Source: Stacks Project, Varieties, Lemma 33.45.6, Tag 0BES, used in Tag 0BEV
(blueprint: lem-sc-top-dimensional-reduction-intersection).

Proof:
1. Apply `lem-sc-numerical-polynomial-leading-term` to `i_* O_Z` and the d invertible
modules. Its support is Z. At each component generic point the stalk is `O_{Z,ξ}`;
its length over `O_{X,ξ}` equals its length over the quotient `O_{Z,ξ}`
(`def-weil-pbc-module-length`). Subtracting the generic-length-weighted component Euler
polynomials leaves a polynomial of degree less than d. Comparing coefficients of the
product of the d variables gives the equality by `def-sc-intersection-number`.
2. The same leading-term lemma gives positive finite generic lengths. A nonempty scheme of
finite dimension d has at least one component of dimension d. Hence if all the ample
self-intersection numbers on these components are positive, their finite sum with positive
weights is positive. This also covers d = 0, where the monomial is the constant monomial. -/
theorem intersectionNumber_topDimensionalReduction
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (Z : Scheme.{u}) [Nonempty Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z = ((d : ℕ∞) : WithBot ℕ∞))
    (r : ℕ)
    (components : Fin r ≃ {C : Set Z // C ∈ irreducibleComponents Z ∧
      topologicalKrullDim C = ((d : ℕ∞) : WithBot ℕ∞)})
    (Y : Fin r → Scheme.{u}) [∀ j, IsIntegral (Y j)]
    (c : ∀ j, Y j ⟶ Z) [∀ j, IsClosedImmersion (c j)]
    (hc : ∀ j, Set.range (c j) = (components j).val)
    (hY : ∀ j, topologicalKrullDim (Y j) = ((d : ℕ∞) : WithBot ℕ∞))
    (ξ : Fin r → Z) (hξ : ∀ j, IsGenericPoint (ξ j) (Set.range (c j)))
    (L : Fin d → X.Modules) [∀ a : Fin d, (L a).IsInvertible] :
    ∃ m : Fin r → ℕ,
      (∀ j, Module.length (Z.presheaf.stalk (ξ j)) (Z.presheaf.stalk (ξ j)) =
        (m j : ℕ∞) ∧ 0 < m j) ∧
      intersectionNumber k X Z i d hd L =
        ∑ j : Fin r, (m j : ℚ) * intersectionNumber k X (Y j) (c j ≫ i) d (hY j) L ∧
      (∀ (A : X.Modules) [A.IsInvertible], IsAmple (X ↘ Spec (.of k)) A →
        (∀ j, 0 < selfIntersectionNumber k X (Y j) (c j ≫ i) d (hY j) A) →
        0 < selfIntersectionNumber k X Z i d hd A) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
