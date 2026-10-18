/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension

import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace
import Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg
import Sheaf.RingTheory.FiniteTypeFibreComponentLowerBound

/-!
# Independent generic linear combinations from a codimension-two intersection

Source: Stacks Project, More on Morphisms, Tag 0G4E, `lemma-algebraically-independent`
(blueprint: lem-zl-bertini-independent-functions).

The component is a subset of the common zero locus with its subspace topology.
Its dimension condition is written additively to avoid truncated subtraction.
The family is indexed by `Fin n ⊕ Fin 2`: the variables, the universal linear
combination, and the scalar linear combination, all in `Frac(Frac(A)[x₁,...,xₙ])`.
-/

@[expose] public section

universe u v

open scoped BigOperators

namespace Algebra

/-- A codimension-two component of `V(g₁,g₂)` supplies an algebraically independent
family consisting of the variables, their `g`-linear combination, and a scalar
linear combination of the `g i`.

Source: Stacks Project, More on Morphisms, Tag 0G4E, `lemma-algebraically-independent`
(blueprint: lem-zl-bertini-independent-functions).

Proof:
1. Set C = A[x₁,...,xₙ], h = sum gᵢxᵢ, and B = k[X₁,...,Xₙ,Y,Z]. Map B to C by
   Xᵢ ↦ xᵢ, Y ↦ h, Z ↦ g₂. Both polynomial rings are domains. The inclusions
   A → Frac(A) and C → Frac(A)[x₁,...,xₙ] → Frac(Frac(A)[x₁,...,xₙ]) are injective,
   so independence of the indicated family is equivalent to this map having zero kernel.
2. Write d = dim A, finite by lem-weil-pbc-finite-type-domain-dimension-trdeg.
   Finite type implies Noetherianity (lem-wf-affine-noetherian-components).
   The polynomial dimension theorem (lem-sf-noetherian-polynomial-dimension) gives
   dim C = d+n and dim B = n+2, since dim k = 0.
3. At the rational maximal ideal m = (X₁-1,X₂,...,Xₙ,Y,Z), the extended ideal in C
   equals (x₁-1,x₂,...,xₙ,g₁,g₂), using h-g₁ = g₁(x₁-1) + sum_{i>1} gᵢxᵢ.
   Evaluation identifies C/mC with A/(g₁,g₂). Its spectrum is homeomorphic to
   V(g₁,g₂), so the hypothesis supplies a fibre component of dimension d-2.
4. If the kernel P were nonzero, it would be a proper prime ideal. Prepending (0)
   to any prime chain above P shows dim(B/P) ≤ n+1.
5. Apply lem-zl-finite-type-fibre-component-lower-bound to B → C and m. The chosen
   component would have dimension at least dim C - dim(B/P) ≥ d-1, contradicting
   dimension d-2. Hence the kernel is zero.
6. Choose c₂ = 1 and cᵢ = 0 for i ≠ 2, so sum cᵢgᵢ = g₂. The zero-kernel conclusion
   gives the asserted algebraic independence. Only 0 and 1 are used, including over finite k.
-/
theorem bertini_independent_functions
    (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Algebra k A] [FiniteType k A] [IsDomain A]
    (n : ℕ) (hn : 2 ≤ n) (g : Fin n → A)
    (hcomp : ∃ W : Set (PrimeSpectrum.zeroLocus
        ({g ⟨0, Nat.zero_lt_of_lt hn⟩, g ⟨1, hn⟩} : Set A)),
      W ∈ irreducibleComponents (PrimeSpectrum.zeroLocus
        ({g ⟨0, Nat.zero_lt_of_lt hn⟩, g ⟨1, hn⟩} : Set A)) ∧
      topologicalKrullDim W + 2 = ringKrullDim A) :
    ∃ c : Fin n → k,
      AlgebraicIndependent k
        (fun j : Fin n ⊕ Fin 2 ↦
          algebraMap (MvPolynomial (Fin n) (FractionRing A))
            (FractionRing (MvPolynomial (Fin n) (FractionRing A)))
            (match j with
            | Sum.inl i => MvPolynomial.X i
            | Sum.inr i =>
                Fin.cases
                  (∑ i : Fin n,
                    MvPolynomial.C (algebraMap A (FractionRing A) (g i)) *
                      MvPolynomial.X i)
                  (fun _ ↦ MvPolynomial.C
                    (∑ i : Fin n,
                      algebraMap k (FractionRing A) (c i) *
                        algebraMap A (FractionRing A) (g i))) i)) := by
  sorry

end Algebra
