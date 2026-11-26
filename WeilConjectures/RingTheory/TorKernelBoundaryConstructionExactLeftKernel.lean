/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.TorKernelBoundaryConstruction
import WeilConjectures.RingTheory.TorKernelBoundaryHorseshoeComparison
import all WeilConjectures.AlgebraicGeometry.TorLongExactFirstVariable

/-!
# Exactness on the left of the constructed Tor boundary

For a surjection `q : F → N`, every class in `Tor₁(N, M)` killed by `torKernelBoundary` comes
from `Tor₁(F, M)`.

## Implementation details

The private resolution and degree-zero homology helpers are imported with `import all` from
`WeilConjectures.AlgebraicGeometry.TorLongExactFirstVariable`; the connecting-map comparison is
proved in `WeilConjectures.RingTheory.TorKernelBoundaryHorseshoeComparison`.

The argument chooses free resolutions of `ker q`, `F`, `N` forming an augmentation-compatible
degreewise split short exact sequence, tensors it with `M` and uses the exact homology sequence.
With the snake convention used, the transported connecting map is the negative of
`torKernelBoundary`; the choice of the augmentation lift does not matter on cycles, and
negation does not change kernels. No projectivity of `F` is required.

## References

* [Stacks, Tag 065P]
* [Stacks, Tag 00M0]
* [Stacks, Tag 00LZ]
* [Stacks, Tag 0111]
-/

@[expose] public section
universe u
open CategoryTheory
open scoped TensorProduct
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- Kernel-to-range inclusion for the constructed Tor boundary: every `y` in `Tor₁(N, M)` with
`torKernelBoundary y = 0` lies in the image of `Tor₁(q, M)`. -/
theorem tor_kernel_boundary_construction_exact_left_kernel
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (F N : ModuleCat.{u} R) (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    ∀ y, torKernelBoundary M F N q hq y = 0 →
      y ∈ Set.range (((Tor' (ModuleCat.{u} R) 1).map
        (ModuleCat.ofHom q)).app M).hom := by
  classical
  let i := (LinearMap.ker q).subtype
  have hi : Function.Injective i := Subtype.val_injective
  have hiq : Function.Exact i q := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact x.property
  obtain ⟨A, B, C, a, b, w, ha, hb, hs⟩ := resolutionSES i q hi hq hiq
  let T := (MonoidalCategory.tensoringRight (ModuleCat R)).obj M
  let S := (ShortComplex.mk a b w).map (T.mapHomologicalComplex (ComplexShape.down ℕ))
  have hS : S.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    exact ((hs n).some.map T).shortExact
  have hcompare := tor_kernel_boundary_horseshoe_comparison R M F N q hq
    A B C a b w ha hb hs hS
  let eB := B.isoLeftDerivedObj T 1
  let eC := C.isoLeftDerivedObj T 1
  let eA := homologyZeroIso A T
  have hnat : (((Tor' (ModuleCat R) 1).map (ModuleCat.ofHom q)).app M) ≫
      eC.hom = eB.hom ≫ HomologicalComplex.homologyMap S.g 1 :=
    B.isoLeftDerivedObj_hom_naturality (ModuleCat.ofHom q) C b hb T 1
  have hex : Function.Exact (HomologicalComplex.homologyMap S.g 1).hom
      (hS.δ 1 0 (by simp)).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₃ 1 0 (by simp))
  intro y hy
  have hz : (hS.δ 1 0 (by simp)).hom (eC.hom.hom y) = 0 := by
    apply (ModuleCat.mono_iff_injective eA.hom).mp inferInstance
    have hh := congrArg (fun f ↦ f.hom y) hcompare
    change eA.hom.hom ((hS.δ 1 0 (by simp)).hom (eC.hom.hom y)) = _ at hh
    change eA.hom.hom ((hS.δ 1 0 (by simp)).hom (eC.hom.hom y)) =
      -(torKernelBoundary M F N q hq y) at hh
    simpa only [hy, neg_zero, map_zero] using hh
  obtain ⟨x, hx⟩ := (hex (eC.hom.hom y)).mp hz
  refine ⟨eB.inv.hom x, ?_⟩
  apply (ModuleCat.mono_iff_injective eC.hom).mp inferInstance
  have hh := congrArg (fun f ↦ f.hom (eB.inv.hom x)) hnat
  change (eC.hom.hom ((((Tor' (ModuleCat R) 1).map
    (ModuleCat.ofHom q)).app M).hom (eB.inv.hom x))) = _ at hh
  rw [hh]
  have he : eB.hom.hom (eB.inv.hom x) = x :=
    congrArg (fun f ↦ f.hom x) eB.inv_hom_id
  change (HomologicalComplex.homologyMap S.g 1).hom
    (eB.hom.hom (eB.inv.hom x)) = eC.hom.hom y
  rw [he]
  exact hx

end CategoryTheory
