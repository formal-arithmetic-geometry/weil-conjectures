/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.SymmetricAlgebraFinitePresentation

/-!
# Smoothness of the symmetric algebra of a finite projective module

The symmetric algebra of a finite projective module is smooth over the base ring
(`SymmetricAlgebra.smooth_of_finite_projective`).

## Implementation details

Finite presentation comes from `SymmetricAlgebra.generators_and_finitePresentation`. Formal
smoothness is checked by infinitesimal lifting: an algebra map out of the symmetric algebra is
determined by a linear map out of `M`, and linear maps from a projective module lift along
surjections.

## References

* [Stacks, Tag 07M6], the implication from finite projective to smooth
-/

@[expose] public section

universe u v

namespace SymmetricAlgebra

/-- The symmetric algebra of a finite projective module is smooth over its base ring. -/
theorem smooth_of_finite_projective (A : Type u) [CommRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] : Algebra.Smooth A (SymmetricAlgebra A M) := by
  -- Formal smoothness via infinitesimal lifting and projectivity of `M`.
  have hfp : Module.FinitePresentation A M := Module.finitePresentation_of_projective A M
  have hfin : Algebra.FinitePresentation A (SymmetricAlgebra A M) :=
    ((generators_and_finitePresentation A M).2 hfp).1
  refine ⟨?_, hfin⟩
  apply Algebra.FormallySmooth.of_comp_surjective
  intro B _ _ I _ f
  obtain ⟨g, hg⟩ := Module.projective_lifting_property
    (Ideal.Quotient.mkₐ A I).toLinearMap (f.toLinearMap.comp (ι A M))
    Ideal.Quotient.mk_surjective
  refine ⟨lift g, ?_⟩
  apply algHom_ext
  ext m
  simpa using LinearMap.congr_fun hg m

end SymmetricAlgebra
