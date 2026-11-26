/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.TorKernelBoundaryConstruction
import WeilConjectures.RingTheory.TorKernelBoundaryConstructionExactLeftKernel
import WeilConjectures.RingTheory.TorKernelBoundaryConstructionExactLeftRange

/-!
# Exactness at Tor for the constructed kernel connecting map

For a surjection `q : F → N`, the sequence `Tor₁(F, M) → Tor₁(N, M) → ker q ⊗ M` formed with
`torKernelBoundary` is exact at `Tor₁(N, M)`.

## Implementation details

The two inclusions are proved separately in `TorKernelBoundaryConstructionExactLeftKernel` and
`TorKernelBoundaryConstructionExactLeftRange`. The underlying argument compares
`torKernelBoundary` with the (negated) snake connecting map of a split short exact sequence of
resolutions of `0 → ker q → F → N → 0` tensored with `M`. No projectivity of `F` is required.

## References

* [Stacks, Tag 00M0]
* [Stacks, Tag 00LZ]
* [Stacks, Tag 0111]
-/

@[expose] public section
universe u
open CategoryTheory
open scoped TensorProduct
namespace CategoryTheory

/-- Exactness of the constructed boundary at Tor: the kernel of `torKernelBoundary` on
`Tor₁(N, M)` is the image of `Tor₁(q, M) : Tor₁(F, M) → Tor₁(N, M)`. -/
theorem tor_kernel_boundary_construction_exact_left
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (F N : ModuleCat.{u} R) (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    Function.Exact (((Tor' (ModuleCat.{u} R) 1).map
      (ModuleCat.ofHom q)).app M).hom (torKernelBoundary M F N q hq) := by
  intro y
  constructor
  · exact tor_kernel_boundary_construction_exact_left_kernel R M F N q hq y
  · rintro ⟨x, rfl⟩
    exact tor_kernel_boundary_construction_exact_left_range R M F N q hq x

end CategoryTheory
