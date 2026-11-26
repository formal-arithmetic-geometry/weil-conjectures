/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Zero-dimensional local rings with separably closed residue field

A local ring of Krull dimension zero with separably closed residue field is strictly henselian,
and idempotents lift uniquely modulo the extended maximal ideal in every finite algebra
(`isStrictlyHenselianLocalRing_of_ringKrullDim_eq_zero`).

## Implementation details

The maximal ideal of a zero-dimensional local ring is its nilradical, so its extension to any
algebra is a nil ideal. Idempotent lifting then follows from Mathlib's
`existsUnique_isIdempotentElem_eq_of_ker_isNilpotent`, without any finiteness assumption, and
henselianity follows from `henselianLocalRing_of_maximalIdeal_le_nilradical`.

## References

* [Stacks, Tag 06RS]
* [Stacks, Tag 00J9]
* [Stacks, Tag 04GG]
* [Stacks, Tag 04GF]
-/

@[expose] public section

universe u v

/-- Over a dimension-zero local ring `R`, idempotents lift uniquely along the quotient of any
`R`-algebra by the extended maximal ideal. -/
private theorem lift_idempotent_of_dimension_zero
    (R : Type u) [CommRing R] [IsLocalRing R] (hdim : ringKrullDim R = 0)
    (B : Type v) [CommRing B] [Algebra R B]
    (e : B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B))
    (he : IsIdempotentElem e) :
    ∃! b : B, IsIdempotentElem b ∧
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R B)) b = e := by
  have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr (by simp [hdim])
  have hnil : (IsLocalRing.maximalIdeal R).map (algebraMap R B) ≤ nilradical B := by
    rw [Ideal.map_le_iff_le_comap, ← Ring.KrullDimLE.nilradical_eq_maximalIdeal]
    intro x hx
    exact (show IsNilpotent x from hx).map (algebraMap R B)
  apply existsUnique_isIdempotentElem_eq_of_ker_isNilpotent
    (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R B)))
    (fun x hx ↦ hnil (by simpa using hx)) e _ he
  exact RingHom.mem_range.mpr (Ideal.Quotient.mk_surjective e)

/-- A zero-dimensional local ring with separably closed residue field is strictly henselian;
idempotents lift uniquely in every finite algebra modulo the extended maximal ideal. -/
theorem isStrictlyHenselianLocalRing_of_ringKrullDim_eq_zero
    (R : Type u) [CommRing R] [IsLocalRing R] (hdim : ringKrullDim R = 0)
    [IsSepClosed (IsLocalRing.ResidueField R)] :
    IsStrictlyHenselianLocalRing R ∧
      ∀ (B : Type v) [CommRing B] [Algebra R B] [Module.Finite R B],
        ∀ e : B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B),
          IsIdempotentElem e →
            ∃! b : B, IsIdempotentElem b ∧
              Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R B)) b = e := by
  have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr (by simp [hdim])
  have hhens : HenselianLocalRing R :=
    henselianLocalRing_of_maximalIdeal_le_nilradical R
      (by rw [Ring.KrullDimLE.nilradical_eq_maximalIdeal])
  refine ⟨(isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed R).mpr
    ⟨hhens, inferInstance⟩, ?_⟩
  intro B _ _ _ e he
  exact lift_idempotent_of_dimension_zero R hdim B e he
