/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

import Sheaf.RingTheory.CompletionFiniteExtension
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Completed fibre presentation for a specified finite coefficient extension

Source: Stacks Project, More on Algebra, Tag 07PU, first paragraph;
Algebra, Tag 07N9.
-/

@[expose] public section

universe u

namespace Polynomial

/-- Base-changing a completed polynomial fibre through a specified finite coefficient
extension gives the product indexed by primes over q which contain the specified s.
The residue-field equivalence must commute with the original polynomial map.
Source: Stacks Project, More on Algebra, Tag 07PU, first paragraph;
Algebra, Tag 07N9.
(blueprint: lem-weil-pbc-polynomial-completed-fibre-compatible-product)

Proof:
The coefficient extension A to B is finite, so A[X] to B[X] is finite. Apply
completion_finite_extension at q to obtain the finite product of the completions
of B[X] at all primes over q. These primes are maximal, by integrality. Each
contracts in B to its maximal ideal: its contraction is a prime above the maximal
ideal of A, hence maximal by integrality, and B is local.
The compatibility equation identifies the A[X]-algebra L with the restriction
of the B[X]-algebra kappa(s). Tensor cancellation identifies
L tensor over kappa(r) with the r-fibre of the completion with
kappa(s) tensor over B[X] with the completed coefficient base change.
Tensor distributes over the finite product, giving the s-fibres of its factors.
If s is not contained in a prime over q, choose an element of s outside that
prime. It is a unit in the localization and its completion, while its image
in kappa(s) is zero. In the tensor product this forces 1 = 0, so that factor
is the zero ring. Restricting to the subset of primes containing s is a ring
isomorphism; its inverse inserts zero in every discarded coordinate. Enumerate
the retained finite subset by Fin n. The displayed isomorphism and all the ideal
relations now follow. When the retained subset is empty, the isomorphism itself
says the source is the zero ring; an empty family is never chosen arbitrarily. -/
theorem completed_fibre_compatible_product
    (A B : Type u) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsLocalRing A] [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing B] [IsLocalRing B]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A)
    (r : Ideal (Polynomial A)) [r.IsPrime]
    (L : Type u) [Field L] [Algebra r.ResidueField L]
    (s : Ideal (Polynomial B)) [s.IsPrime] [Algebra B L]
    (e : s.ResidueField ≃ₐ[B] L)
    (he : ∀ f : Polynomial A,
      e (algebraMap (Polynomial B) s.ResidueField
        (Polynomial.map (algebraMap A B) f)) =
        algebraMap r.ResidueField L (algebraMap (Polynomial A) r.ResidueField f)) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    ∃ (n : ℕ) (q' : Fin n → Ideal (Polynomial B))
      (qmax : ∀ i, (q' i).IsMaximal),
      letI := qmax
      (∀ i, (q' i).comap (Polynomial.C : B →+* Polynomial B) =
        IsLocalRing.maximalIdeal B) ∧
      (∀ i, s ≤ q' i) ∧
      Nonempty ((TensorProduct r.ResidueField L (r.Fiber C)) ≃+*
        (∀ i : Fin n, s.Fiber
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime (q' i)))
            (Localization.AtPrime (q' i))))) := by
  sorry

end Polynomial
