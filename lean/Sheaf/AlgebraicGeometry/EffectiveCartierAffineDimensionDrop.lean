/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.KrullDimension.Regular
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRing

/-! # Dimension drop for a principal Cartier subscheme of an affine variety

Source: literature/stacks-project/algebra.tex, Tags 00KV and 00KW (Krull principal ideal
and height theorems), Tags 00OS and 00P0 (finite-type domain dimensions), and
literature/stacks-project/morphisms.tex, Tag 02FX (finite-type fibre dimension formula)
(blueprint: lem-sc-effective-cartier-affine-dimension-drop).
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- Since a nonzero nonunit cuts an integral finite-type affine scheme by codimension one,
its principal quotient has Krull dimension one less.

Source: literature/stacks-project/algebra.tex, Tags 00KV, 00KW, 00OS and 00P0;
literature/stacks-project/morphisms.tex, Tag 02FX.
(blueprint: lem-sc-effective-cartier-affine-dimension-drop).

Proof: integrality of the spectrum makes `A` a domain, and finite type over the field
makes it Noetherian. Choose a maximal ideal `m` containing the proper ideal `(f)`.
Its height equals the dimension of `A`, by the finite-type domain theorem and
Mathlib's identification of height with the dimension of a prime localization.
Apply Mathlib's principal-quotient dimension theorem for a nonzerodivisor contained
in a prime of full height. Finally identify spectrum dimensions with ring dimensions.
-/
theorem effective_cartier_affine_dimension_drop
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [IsIntegral (Spec (CommRingCat.of A))]
    (f : A) (hf0 : f ≠ 0) (hfu : ¬ IsUnit f) :
    topologicalKrullDim
        (AlgebraicGeometry.Spec (CommRingCat.of (A ⧸ Ideal.span ({f} : Set A)))) + 1 =
      topologicalKrullDim (AlgebraicGeometry.Spec (CommRingCat.of A)) := by
  have : IsDomain A := (affine_isIntegral_iff (CommRingCat.of A)).mp inferInstance
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨m, hm, hfm⟩ := (Ideal.span ({f} : Set A)).exists_le_maximal
    (fun h ↦ hfu (Ideal.span_singleton_eq_top.mp h))
  have : m.IsMaximal := hm
  have hheight : (m.height : WithBot ℕ∞) = ringKrullDim A := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
    exact (finiteTypeDomain_ringKrullDim_localizationAtMaximal (k := k) (S := A)).1 m
  change topologicalKrullDim (PrimeSpectrum (A ⧸ Ideal.span ({f} : Set A))) + 1 =
    topologicalKrullDim (PrimeSpectrum A)
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hf0) hheight
    (hfm (Ideal.subset_span (Set.mem_singleton f)))

end AlgebraicGeometry
