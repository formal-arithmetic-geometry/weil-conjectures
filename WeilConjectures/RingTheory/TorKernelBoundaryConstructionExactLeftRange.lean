/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.TorKernelBoundaryConstruction
import WeilConjectures.RingTheory.TorKernelBoundaryNaturalityOf

/-!
# The constructed Tor boundary vanishes on the image of `Tor₁(q, M)`

For a surjection `q : F → N`, `torKernelBoundary` vanishes on the image of
`Tor₁(q, M) : Tor₁(F, M) → Tor₁(N, M)`.

## Implementation details

This follows from naturality of the constructed boundary, applied to the morphism from the
identity presentation `F → F` to `q : F → N`, whose map on kernels is zero.

## References

* [Stacks, Tag 00LZ]
* [Stacks, Tag 00M0]
-/

@[expose] public section
universe u
open CategoryTheory
open scoped TensorProduct
namespace CategoryTheory

/-- The constructed boundary vanishes on the image of Tor of the quotient map:
`torKernelBoundary (Tor₁(q, M) x) = 0` for every `x` in `Tor₁(F, M)`. -/
theorem tor_kernel_boundary_construction_exact_left_range
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (F N : ModuleCat.{u} R) (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    ∀ x, torKernelBoundary M F N q hq
      ((((Tor' (ModuleCat.{u} R) 1).map
        (ModuleCat.ofHom q)).app M).hom x) = 0 := by
  intro x
  have h := tor_kernel_boundary_naturality_of R M F F F N
    (LinearMap.id : F →ₗ[R] F) q Function.surjective_id hq
    LinearMap.id q (0 : LinearMap.ker (LinearMap.id : F →ₗ[R] F) →ₗ[R] LinearMap.ker q)
    (by simp) (by
      intro z
      have hz : (z : F) = 0 := z.property
      simp [hz]) x
  simpa using h

end CategoryTheory
