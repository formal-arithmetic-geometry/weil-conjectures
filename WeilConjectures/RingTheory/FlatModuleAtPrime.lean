/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness

/-!
# Flat modules localized at a prime of an algebra

Source: Stacks Project, Algebra, Lemma 10.39.18 (Tag 00HT), part (6), only-if direction
(blueprint: lem-pc-affine-flat-module-local-criterion).
-/

@[expose] public section

/-- Variant of `Module.Flat.localizedModule_of_algebra` for additive commutative monoids
(blueprint: lem-pc-affine-flat-module-localization-preserves-flatness). -/
theorem localizedModule_of_algebra_of_addCommMonoid {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommMonoid M] [Module R M] [Module A M]
    [IsScalarTower R A M] (S : Submonoid A) (hM : Module.Flat R M) :
    Module.Flat R (LocalizedModule S M) := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ N
  let g : M →ₗ[A] LocalizedModule S M := LocalizedModule.mkLinearMap S M
  have hinj : Function.Injective (LinearMap.lTensor M N.subtype) :=
    hM.lTensor_preserves_injective_linearMap N.subtype N.subtype_injective
  have hinjA : Function.Injective
      (TensorProduct.AlgebraTensorModule.lTensor A M N.subtype) := by
    simpa only [TensorProduct.AlgebraTensorModule.coe_lTensor] using hinj
  have hloc := IsLocalizedModule.map_injective S
    (TensorProduct.AlgebraTensorModule.rTensor R N g)
    (TensorProduct.AlgebraTensorModule.rTensor R P g)
    (TensorProduct.AlgebraTensorModule.lTensor A M N.subtype) hinjA
  rw [IsLocalizedModule.map_lTensor] at hloc
  simpa only [TensorProduct.AlgebraTensorModule.coe_lTensor] using hloc

namespace Module.Flat

/-- Stacks Project, Algebra, Lemma 10.39.18 (Tag 00HT), part (6), only-if direction
(blueprint: lem-pc-affine-flat-module-local-criterion). Fix `q` and contract it to `p` in `R`.
Localizing the `A`-module `M` away from `q` preserves its flatness over `R` by
`lem-pc-affine-flat-module-localization-preserves-flatness`. Every element outside `p`
maps to a unit in `A_q`, giving `M_q` its `R_p`-module structure. Finally,
`lem-weil-pbc-flat-over-localization` identifies flatness of this module over `R` with
flatness over `R_p`. -/
theorem localizedModule_atPrime_of_flat {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommMonoid M] [Module A M] (q : Ideal A) [q.IsPrime]
    (hflat : @Module.Flat R M _ _ (Module.compHom M (algebraMap R A))) :
    @Module.Flat (Localization.AtPrime (q.comap (algebraMap R A)))
      (LocalizedModule q.primeCompl M) _ _
      (Module.compHom _ (Localization.localRingHom (q.comap (algebraMap R A)) q
        (algebraMap R A) rfl)) := by
  let : Module R M := Module.compHom M (algebraMap R A)
  have : IsScalarTower R A M := ⟨fun r a m => by
    change (r • a) • m = algebraMap R A r • a • m
    rw [Algebra.smul_def, mul_smul]⟩
  have hR := localizedModule_of_algebra_of_addCommMonoid q.primeCompl hflat
  set p := q.comap (algebraMap R A)
  let : Module (Localization.AtPrime p) (LocalizedModule q.primeCompl M) :=
    Module.compHom _ (Localization.localRingHom p q (algebraMap R A) rfl)
  have : IsScalarTower R (Localization.AtPrime p) (LocalizedModule q.primeCompl M) :=
    ⟨fun r x m => by
      change Localization.localRingHom p q (algebraMap R A) rfl (r • x) • m =
        r • (Localization.localRingHom p q (algebraMap R A) rfl x • m)
      rw [Algebra.smul_def, map_mul, Localization.localRingHom_to_map, mul_smul,
        IsScalarTower.algebraMap_smul, algebraMap_smul]⟩
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl _).2 hR

end Module.Flat
