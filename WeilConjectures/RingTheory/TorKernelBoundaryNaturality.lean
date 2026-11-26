/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.RingTheory.TorKernelBoundaryConstructionExact
import WeilConjectures.RingTheory.TorKernelBoundaryNaturalityOf

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct

namespace CategoryTheory

/-!
# The Tor boundary for kernels, natural in presentations

For a surjection `q : F → N` of `R`-modules we construct the boundary map
`Tor₁(N, M) → ker q ⊗ M`, exact in the low-degree Tor sequence and natural in `q`.

## Implementation details

For each surjection `q`, the short exact sequence `0 → ker q → F → N → 0` is lifted to a
degreewise split short exact sequence of free resolutions and tensored with `M`; the homology
connecting map followed by the augmentation identification `H₀ = ker q ⊗ M` defines the boundary.
Naturality follows by lifting morphisms of short exact sequences to the resolutions; independence
of lifts up to chain homotopy identifies the induced maps with `Tor'(b, M)` and `c ⊗ 1`.

## References

* [Stacks, Tag 00M0]
* [Stacks, Section 00LY]
-/

/-- Choose the low-degree boundary simultaneously for all surjective presentations,
with exactness at Tor one and at the tensor of the kernel, and naturality in the
first variable. No projectivity or minimality of the presentation is assumed. -/
theorem exists_tor_kernel_boundary_natural
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R) :
    ∃ δ : ∀ (F N : ModuleCat.{u} R) (q : F →ₗ[R] N),
        Function.Surjective q →
          (((Tor' (ModuleCat.{u} R) 1).obj N).obj M) →ₗ[R]
            (LinearMap.ker q ⊗[R] M),
      (∀ (F N : ModuleCat.{u} R) (q : F →ₗ[R] N) (hq : Function.Surjective q),
        Function.Exact (((Tor' (ModuleCat.{u} R) 1).map
          (ModuleCat.ofHom q)).app M).hom (δ F N q hq) ∧
        Function.Exact (δ F N q hq) ((LinearMap.ker q).subtype.rTensor M)) ∧
      (∀ (F N F' N' : ModuleCat.{u} R) (q : F →ₗ[R] N) (q' : F' →ₗ[R] N')
          (hq : Function.Surjective q) (hq' : Function.Surjective q')
          (a : F →ₗ[R] F') (b : N →ₗ[R] N')
          (c : LinearMap.ker q →ₗ[R] LinearMap.ker q'),
        q'.comp a = b.comp q →
        (∀ x : LinearMap.ker q, (c x : F') = a (x : F)) →
        ∀ t : (((Tor' (ModuleCat.{u} R) 1).obj N).obj M),
          δ F' N' q' hq' ((((Tor' (ModuleCat.{u} R) 1).map
            (ModuleCat.ofHom b)).app M).hom t) =
          c.rTensor M (δ F N q hq t)) := by
  refine ⟨torKernelBoundary M, ?_, tor_kernel_boundary_naturality_of R M⟩
  intro F N q hq
  exact tor_kernel_boundary_construction_exact R M F N q hq

end CategoryTheory
