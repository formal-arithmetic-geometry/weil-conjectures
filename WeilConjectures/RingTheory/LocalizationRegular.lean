/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Localization maps are regular

Every localization map `S → W⁻¹S` is a regular ring map. Its fibre at a prime disjoint from `W`
is the residue field, and its other fibres are zero.

## Implementation details

Localization is flat. Base change identifies the fibre at `p` with a localization of the residue
field at the image of `W`, which is the residue field itself if `W` misses `p` (all images are
units) and the zero ring otherwise. Both are geometrically regular, since base change to a finite
purely inseparable extension gives a field or the zero ring.

## References

* [Stacks, Tag 07PT] (proof)
* [Stacks, Tag 07BZ]
* [Stacks, Tags 00HT, 00DK, 00CQ, 00CP, 0381, 0382]
-/

@[expose] public section

universe u v

namespace IsLocalization

private theorem regular_of_field (k : Type*) (A : Type*) [Field k] [CommRing A]
    [Algebra k A] (M : Submonoid k) [IsLocalization M A] : IsRegularRing A := by
  classical
  by_cases h : (0 : k) ∈ M
  · have : Subsingleton A := (IsLocalization.subsingleton_iff).mpr h
    refine ⟨fun p hp ↦ ?_⟩
    exact False.elim (hp.ne_top (Subsingleton.elim p ⊤))
  · have hu : M ≤ IsUnit.submonoid k := by
      intro x hx
      exact isUnit_iff_ne_zero.mpr (fun e ↦ h (e ▸ hx))
    exact IsRegularRing.of_ringEquiv (IsLocalization.atUnits k M hu).toRingEquiv

/-- Every localization map is regular. Its fibre at a prime disjoint from the denominators
is the residue field as an algebra over that field; otherwise its fibre is the zero ring. -/
theorem isRegular_and_fiber
    {S : Type u} {T : Type v} [CommRing S] [CommRing T] [Algebra S T]
    (W : Submonoid S) [IsLocalization W T] :
    RingHom.IsRegular (algebraMap S T) ∧
      ∀ (p : Ideal S) [p.IsPrime],
        ((∀ w : W, (w : S) ∉ p) → Nonempty (p.Fiber T ≃ₐ[p.ResidueField] p.ResidueField)) ∧
        ((∃ w : W, (w : S) ∈ p) → Subsingleton (p.Fiber T)) := by
  classical
  have hf (p : Ideal S) [p.IsPrime] :
      ((∀ w : W, (w : S) ∉ p) →
        Nonempty (p.Fiber T ≃ₐ[p.ResidueField] p.ResidueField)) ∧
      ((∃ w : W, (w : S) ∈ p) → Subsingleton (p.Fiber T)) := by
    let M := Algebra.algebraMapSubmonoid p.ResidueField W
    have : IsLocalization M (p.Fiber T) := IsLocalization.tensor T W
    constructor
    · intro h
      have hu : M ≤ IsUnit.submonoid p.ResidueField := by
        rintro x ⟨w, hw, rfl⟩
        exact isUnit_iff_ne_zero.mpr (fun e ↦ h ⟨w, hw⟩
          (Ideal.algebraMap_residueField_eq_zero.mp e))
      exact ⟨(IsLocalization.atUnits p.ResidueField M hu).symm⟩
    · rintro ⟨w, hw⟩
      apply (IsLocalization.subsingleton_iff (M := M) (S := p.Fiber T)).mpr
      exact ⟨w, w.prop, Ideal.algebraMap_residueField_eq_zero.mpr hw⟩
  refine ⟨?_, hf⟩
  rw [RingHom.IsRegular, toAlgebra_algebraMap]
  refine ⟨RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat T W), ?_⟩
  intro p hp
  let M := Algebra.algebraMapSubmonoid p.ResidueField W
  have : IsLocalization M (p.Fiber T) := IsLocalization.tensor T W
  have : IsRegularRing (p.Fiber T) := regular_of_field p.ResidueField (p.Fiber T) M
  refine ⟨inferInstance, ?_⟩
  intro k' _ _ _ _
  exact regular_of_field k' (TensorProduct p.ResidueField k' (p.Fiber T))
    (Algebra.algebraMapSubmonoid k' M)

end IsLocalization
