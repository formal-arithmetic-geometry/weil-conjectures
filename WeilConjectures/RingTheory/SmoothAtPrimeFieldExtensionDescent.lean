/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.RingTheory.SmoothAtPrimeFieldExtensionDescentAux


/-!
# Descent of smoothness at a prime along a field extension

For a finite type algebra over a field `k` and a field extension `K/k`, smoothness of the base
change to `K` at a prime implies smoothness over `k` at the contracted prime.

## References

* [Stacks, Tag 02UQ]
* [Stacks, Tag 00TG]
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- For a finite type `k`-algebra `S` and a field extension `K/k`, smoothness of
`K ⊗[k] S` over `K` at `qK` implies smoothness of `S` over `k` at the contracted prime.
The `K`-algebra structure sends `λ` to `λ ⊗ 1`, and `includeRight` sends `s` to `1 ⊗ s`. -/
theorem isSmoothAtPrime_of_fieldExtension
    {k : Type u} {K : Type v} {S : Type w}
    [Field k] [Field K] [Algebra k K] [CommRing S] [Algebra k S] [FiniteType k S]
    (qK : PrimeSpectrum (K ⊗[k] S)) (hsmooth : IsSmoothAtPrime K qK) :
    IsSmoothAtPrime k
      (PrimeSpectrum.comap (TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK) := by
  have hfp : FinitePresentation k S := FinitePresentation.of_finiteType.mp inferInstance
  let q := PrimeSpectrum.comap
    (TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK
  have hformal : Algebra.IsSmoothAt k q.asIdeal :=
    formallySmoothAtPrime_of_fieldExtension qK hsmooth
  obtain ⟨g, hg, hsm⟩ :=
    @Algebra.IsSmoothAt.exists_notMem_smooth k S _ _ _ hfp q.asIdeal inferInstance hformal
  exact ⟨g, hg, hsm⟩

end Algebra
