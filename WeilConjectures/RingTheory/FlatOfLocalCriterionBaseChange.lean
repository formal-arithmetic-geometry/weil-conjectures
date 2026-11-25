/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.RingTheory.LocalizedBaseChangeQuotientFlat
import WeilConjectures.RingTheory.LocalizedBaseChangeIdealKernelSpan
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import WeilConjectures.Mathlib.RingTheory.Filtration

/-!
# Another variant of the local criterion of flatness

For a commutative square of local homomorphisms of Noetherian local rings in which `S'` is a
localization of `S ⊗[R] R'`, a finite `S`-module `M` whose quotient `M / IM` is flat over `R / I`
and whose multiplication kernel `I ⊗[R] M → M` dies in the base change has `S' ⊗[S] M` flat
over `R'`.

## Implementation details

The algebra maps are the four maps of the square, and the scalar towers express its
commutativity. `M / IM` is represented by `(R ⧸ I) ⊗[R] M`, canonically isomorphic to it via
`TensorProduct.quotTensorEquivQuotSMul`, and `S' ⊗[S] M` plays the role of `M ⊗[S] S'`.

The proof identifies `M' = S' ⊗[S] M` with a localization of `R' ⊗[R] M`, shows that
`M' / I'M'` is flat over `R' / I'` by base change, and that the multiplication kernel for `M'`
is a localization of a quotient of the base change of the original kernel, hence zero by the
hypothesis on `θ`. The variant of the local criterion then applies.

## References

* [Stacks, Tag 00MO]
* [Stacks, Tag 00M6]
-/

@[expose] public section

universe u v w z t

open scoped TensorProduct

namespace Module

/-- The local criterion after a localization of base change: let `S'` be a localization of
`S ⊗[R] R'` and `M` a finite `S`-module. If `M / IM` is flat over `R / I` and the map `θ`
induced by `I ⊗[R] M → I R' ⊗[R'] (S' ⊗[S] M)` kills the kernel of multiplication
`I ⊗[R] M → M`, then `S' ⊗[S] M` is flat over `R'`.

The quotient is represented by `(R ⧸ I) ⊗[R] M`, and `θ` is specified on pure tensors, which
determines it uniquely. -/
theorem flat_of_local_criterion_baseChange
    {R : Type u} {S : Type v} {R' : Type w} {S' : Type z}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    [IsNoetherianRing R] [IsNoetherianRing S]
    [IsNoetherianRing R'] [IsNoetherianRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R R')]
    [IsLocalHom (algebraMap S S')] [IsLocalHom (algebraMap R' S')]
    (I : Ideal R) (hI : I ≠ ⊤)
    (M : Type t) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] [Module.Finite S M]
    (hloc : ∃ (q : S ⊗[R] R' →+* S') (W : Submonoid (S ⊗[R] R')),
      (∀ (s : S) (r' : R'), q (s ⊗ₜ[R] r') =
        algebraMap S S' s * algebraMap R' S' r') ∧
      (letI := q.toAlgebra; IsLocalization W S'))
    (hquot : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M))
    (θ : I ⊗[R] M →+ (I.map (algebraMap R R')) ⊗[R'] (S' ⊗[S] M))
    (hθ : ∀ (a : I) (x : M), θ (a ⊗ₜ[R] x) =
      (⟨algebraMap R R' a, Ideal.mem_map_of_mem (algebraMap R R') a.property⟩ :
        I.map (algebraMap R R')) ⊗ₜ[R'] ((1 : S') ⊗ₜ[S] x))
    (hker : ∀ k : I ⊗[R] M,
      TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype) k = 0 → θ k = 0) :
    Module.Flat R' (S' ⊗[S] M) := by
  let J := I.map (algebraMap R R')
  let N := S' ⊗[S] M
  have hquot' : Module.Flat (R' ⧸ J) ((R' ⧸ J) ⊗[R'] N) :=
    flat_quotient_localized_baseChange I M hloc hquot
  have : Module.Flat (R' ⧸ J) (N ⧸ J • (⊤ : Submodule R' N)) :=
    Module.Flat.of_linearEquiv
      ((TensorProduct.quotTensorEquivQuotSMul N J).extendScalarsOfSurjective
        Ideal.Quotient.mk_surjective).symm
  have hspan : Submodule.span S'
      ((fun k : I ⊗[R] M ↦ TensorProduct.comm R' J N (θ k)) ''
        (LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)) :
          Set (I ⊗[R] M))) ≤ ⊥ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, hk, rfl⟩
    have hk' := hker k (LinearMap.mem_ker.mp hk)
    simp [hk']
  have hmul : Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul R' N).comp J.subtype)) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have hmem := mem_span_ideal_kernel_localized_baseChange I M hloc hquot θ hθ z hz
    have heq : TensorProduct.comm R' J N z = 0 := hspan hmem
    exact (TensorProduct.comm R' J N).injective (heq.trans (map_zero _).symm)
  have hinj : Function.Injective (J.subtype.lTensor N) := by
    intro x y hxy
    apply (TensorProduct.comm R' N J).injective
    apply hmul
    have hcomm :
        (TensorProduct.lift ((LinearMap.lsmul R' N).comp J.subtype)).comp
            (TensorProduct.comm R' N J).toLinearMap =
          (TensorProduct.rid R' N).toLinearMap.comp (J.subtype.lTensor N) := by
      ext n j
      simp
    change ((TensorProduct.lift ((LinearMap.lsmul R' N).comp J.subtype)).comp
      (TensorProduct.comm R' N J).toLinearMap) x =
        ((TensorProduct.lift ((LinearMap.lsmul R' N).comp J.subtype)).comp
          (TensorProduct.comm R' N J).toLinearMap) y
    rw [hcomm]
    exact congrArg (TensorProduct.rid R' N) hxy
  have hIS : J.map (algebraMap R' S') ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    exact (Ideal.map_mono ((Ideal.map_mono (IsLocalRing.le_maximalIdeal hI)).trans
      (IsLocalRing.map_maximalIdeal_le (algebraMap R R')))).trans
        (IsLocalRing.map_maximalIdeal_le (algebraMap R' S'))
  exact Module.Flat.of_flat_quotient_of_lTensor_injective (S := S') J hIS hinj

end Module
