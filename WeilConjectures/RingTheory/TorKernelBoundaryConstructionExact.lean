/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.TorKernelBoundaryConstruction
import WeilConjectures.RingTheory.TorKernelBoundaryConstructionExactLeft
import WeilConjectures.RingTheory.TorKernelBoundaryConstructionExactRight

/-!
# Exactness for the constructed kernel connecting map

For a surjection `q : F → N` with kernel `K`, the explicitly constructed connecting map
`torKernelBoundary : Tor₁(N, M) → K ⊗ M` fits into the exact sequence
`Tor₁(F, M) → Tor₁(N, M) → K ⊗ M → F ⊗ M`.

## Implementation details

The proof compares `torKernelBoundary` with the snake connecting map of a horseshoe resolution
of `0 → K → F → N → 0` tensored with `M`. With the snake convention used, the transported
connecting map is the negative of the explicit cycle boundary; changing the lift of the
augmentation does not change the boundary on cycles, and negation preserves kernels and images.
The two exactness statements are proved in `TorKernelBoundaryConstructionExactLeft` and
`TorKernelBoundaryConstructionExactRight`. Projectivity of `F` is not needed.

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

/-- Exactness of the explicit cycle boundary, without any naturality assertion: the sequence
`Tor₁(F, M) → Tor₁(N, M) → ker q ⊗ M → F ⊗ M` is exact at `Tor₁(N, M)` and at `ker q ⊗ M`. -/
theorem tor_kernel_boundary_construction_exact
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (F N : ModuleCat.{u} R) (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    Function.Exact (((Tor' (ModuleCat.{u} R) 1).map
      (ModuleCat.ofHom q)).app M).hom (torKernelBoundary M F N q hq) ∧
    Function.Exact (torKernelBoundary M F N q hq)
      ((LinearMap.ker q).subtype.rTensor M) := by
  exact ⟨tor_kernel_boundary_construction_exact_left R M F N q hq,
    tor_kernel_boundary_construction_exact_right R M F N q hq⟩

end CategoryTheory
