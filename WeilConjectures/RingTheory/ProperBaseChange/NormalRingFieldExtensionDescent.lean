/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Flat

/-!
# Descent of normality under scalar field extension

If `B ⊗[F] E` is normal for a field extension `E/F`, then the `F`-algebra `B` is normal.

## Implementation details

The map `B → S = B ⊗[F] E` is faithfully flat. For a prime `p` of `B`, lift it to a prime `q` of
`S`; the induced local map `j : B_p → S_q` is faithfully flat, hence injective, so `B_p` is a
domain. If `x = a/b` is integral over `B_p`, its image is integral over the integrally closed
`S_q`, so `j(a) ∈ j(b) S_q`, and faithfully flat ideal contraction gives `a ∈ b B_p`.

## References

* [Stacks, Tag 033G]
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

private theorem integrallyClosed_of_faithfullyFlat
    (A C : Type*) [CommRing A] [CommRing C] [Algebra A C]
    [Module.FaithfullyFlat A C] [IsDomain A] [IsDomain C] [IsIntegrallyClosed C] :
    IsIntegrallyClosed A := by
  let K := FractionRing A
  let L := FractionRing C
  let g : A →ₐ[A] L := Algebra.ofId A L
  have hg : Function.Injective g :=
    (IsFractionRing.injective C L).comp (FaithfulSMul.algebraMap_injective A C)
  let φ : K →ₐ[A] L := IsFractionRing.liftAlgHom (g := g) hg
  apply (isIntegrallyClosed_iff K).mpr
  intro x hx
  have hy : IsIntegral C (φ x) := (hx.map φ).tower_top
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hy
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hgb0 : g b ≠ 0 := by
    exact (map_ne_zero_iff g hg).mpr hb0
  have heq : algebraMap C L (algebraMap A C a) =
      algebraMap C L (algebraMap A C b * s) := by
    have hφ : φ (algebraMap A K a / algebraMap A K b) = g a / g b := by
      simp [φ, g]
    have he := (div_eq_iff hgb0).mp (hφ.symm.trans hs.symm)
    simpa [g, IsScalarTower.algebraMap_apply A C L, mul_comm] using he
  have heqC : algebraMap A C a = algebraMap A C b * s :=
    IsFractionRing.injective C L heq
  have ha : a ∈ Ideal.span ({b} : Set A) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := C) (Ideal.span ({b} : Set A))]
    change algebraMap A C a ∈ Ideal.map (algebraMap A C) (Ideal.span ({b} : Set A))
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact ⟨s, heqC⟩
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ha
  refine ⟨r, ?_⟩
  rw [hr, map_mul, mul_div_cancel_left₀]
  exact (map_ne_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).mpr hb0

/-- Normality of a commutative algebra descends along an arbitrary scalar field extension.
Normality means that every prime localization is an integrally closed domain. -/
theorem normal_ring_of_normal_tensor_field
    (F : Type u) (E : Type v) (B : Type w)
    [Field F] [Field E] [Algebra F E] [CommRing B] [Algebra F B]
    (h : ∀ (q : Ideal (B ⊗[F] E)) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) :
    ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let S := B ⊗[F] E
  let : Module.FaithfullyFlat F E := inferInstance
  let : Module.FaithfullyFlat B S := inferInstance
  let f : B →+* S := algebraMap B S
  intro p hp
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := S) p
  let : q.IsPrime := hq
  have hcomap : p = Ideal.comap f q := by simpa [f, Ideal.under] using hqp.over
  let j := Localization.localRingHom p q f hcomap
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) := j.toAlgebra
  have hf : f.Flat := by
    rw [show f = algebraMap B S by rfl, RingHom.flat_algebraMap_iff]
    infer_instance
  have hjflat : j.Flat := RingHom.Flat.localRingHom (f := f) hf q p hcomap
  have hjflat' : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) := by
    change RingHom.Flat j
    exact hjflat
  have hflocal : IsLocalHom j := inferInstance
  let : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    change IsLocalHom j
    exact hflocal
  let : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) := hjflat'
  let : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hqnormal := h q
  let : IsDomain (Localization.AtPrime q) := hqnormal.1
  let : IsIntegrallyClosed (Localization.AtPrime q) := hqnormal.2
  have hji := FaithfulSMul.algebraMap_injective
    (Localization.AtPrime p) (Localization.AtPrime q)
  let : IsDomain (Localization.AtPrime p) := Function.Injective.isDomain _ hji
  exact ⟨inferInstance, integrallyClosed_of_faithfullyFlat
    (Localization.AtPrime p) (Localization.AtPrime q)⟩

end Algebra
