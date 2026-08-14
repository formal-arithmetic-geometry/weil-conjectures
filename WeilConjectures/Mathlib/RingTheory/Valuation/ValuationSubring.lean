/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# The composite of two valuation rings

Given a valuation subring `A` of a field `K` and a valuation subring `A''` of the residue
field of `A`, the preimage of `A''` under the residue map of `A` is again a valuation
subring of `K`, the *composite* of the two valuation rings:

- `ValuationSubring.comapResidue`: the composite valuation subring `C ⊆ K`;
- `ValuationSubring.mem_comapResidue_of_not_isUnit`: `C` contains the maximal ideal
  `𝔪'` of `A`;
- `ValuationSubring.residueRestrict`: the residue map of `A` restricted to `C` and
  corestricted to `A''`; it is surjective (`residueRestrict_surjective`) with kernel the
  trace of `𝔪'` (`ker_residueRestrict`), which is the identification `C/𝔪' ≅ A''`.
-/

@[expose] public section

namespace ValuationSubring

open IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K)

/-- The inverse of an element of a valuation subring which is a unit of the subring
belongs to the subring. -/
theorem inv_mem_of_isUnit {x : K} (hx : x ∈ A) (hu : IsUnit (⟨x, hx⟩ : A)) :
    x⁻¹ ∈ A := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u⁻¹ : Aˣ) : A) * ⟨x, hx⟩ = 1 := by
    rw [← hu]
    exact u.inv_mul
  have h2 : (((u⁻¹ : Aˣ) : A) : K) * x = 1 := by
    have := congrArg (Subtype.val : A → K) h1
    simpa using this
  rw [inv_eq_of_mul_eq_one_left h2]
  exact SetLike.coe_mem (((u⁻¹ : Aˣ) : A))

/-- **The composite of two valuation rings**: the preimage in a valuation subring
`A ⊆ K` of a valuation subring `A''` of the residue field of `A` is a valuation subring
of `K`. Its fraction field is `K` (as for every valuation subring of `K`), it contains
the maximal ideal of `A` (`ValuationSubring.mem_comapResidue_of_not_isUnit`), and its
quotient by that ideal is `A''` (`ValuationSubring.residueRestrict_surjective`,
`ValuationSubring.ker_residueRestrict`). -/
def comapResidue (A'' : ValuationSubring (ResidueField A)) : ValuationSubring K where
  __ := (A''.toSubring.comap (residue A)).map A.subtype
  mem_or_inv_mem' := by
    intro x
    by_cases hxA : x ∈ A
    · by_cases hres : residue A ⟨x, hxA⟩ ∈ A''
      · exact Or.inl (Subring.mem_map.mpr ⟨⟨x, hxA⟩, Subring.mem_comap.mpr hres, rfl⟩)
      · -- `x` is a unit of `A`, else its residue would be `0 ∈ A''`
        have hunit : IsUnit (⟨x, hxA⟩ : A) := by
          by_contra hnu
          exact hres (by
            rw [(residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr
              (_root_.mem_nonunits_iff.mpr hnu))]
            exact zero_mem _)
        have hx0 : x ≠ 0 := by
          rintro rfl
          exact hunit.ne_zero (by rfl)
        have hxinvA : x⁻¹ ∈ A := A.inv_mem_of_isUnit hxA hunit
        refine Or.inr (Subring.mem_map.mpr
          ⟨⟨x⁻¹, hxinvA⟩, Subring.mem_comap.mpr ?_, rfl⟩)
        have hmul : residue A ⟨x, hxA⟩ * residue A ⟨x⁻¹, hxinvA⟩ = 1 := by
          rw [← map_mul, show (⟨x, hxA⟩ : A) * ⟨x⁻¹, hxinvA⟩ = 1 from
            Subtype.ext (mul_inv_cancel₀ hx0), map_one]
        rcases A''.mem_or_inv_mem (residue A ⟨x, hxA⟩) with h | h
        · exact absurd h hres
        · change residue A ⟨x⁻¹, hxinvA⟩ ∈ A''
          rwa [show residue A ⟨x⁻¹, hxinvA⟩ = (residue A ⟨x, hxA⟩)⁻¹ from
            eq_inv_of_mul_eq_one_left (mul_comm (residue A ⟨x, hxA⟩) _ ▸ hmul)]
    · -- `x⁻¹` lies in the maximal ideal of `A`, so its residue is `0 ∈ A''`
      have hxinv : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hxA
      have hnu : ¬IsUnit (⟨x⁻¹, hxinv⟩ : A) := by
        intro hu
        have := A.inv_mem_of_isUnit hxinv hu
        rw [inv_inv] at this
        exact hxA this
      refine Or.inr (Subring.mem_map.mpr
        ⟨⟨x⁻¹, hxinv⟩, Subring.mem_comap.mpr ?_, rfl⟩)
      change residue A ⟨x⁻¹, hxinv⟩ ∈ A''
      rw [(residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr
        (_root_.mem_nonunits_iff.mpr hnu))]
      exact zero_mem _

variable (A'' : ValuationSubring (ResidueField A))

theorem mem_comapResidue {x : K} :
    x ∈ A.comapResidue A'' ↔ ∃ hx : x ∈ A, residue A ⟨x, hx⟩ ∈ A'' := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := Subring.mem_map.mp h
    exact ⟨a.2, ha⟩
  · rintro ⟨hx, hres⟩
    exact Subring.mem_map.mpr ⟨⟨x, hx⟩, hres, rfl⟩

/-- The composite valuation ring is contained in `A`. -/
theorem comapResidue_le : (A.comapResidue A'').toSubring ≤ A.toSubring := by
  intro x hx
  exact (mem_comapResidue A A''|>.mp hx).1

/-- The composite valuation ring contains the maximal ideal of `A`. -/
theorem mem_comapResidue_of_not_isUnit {x : K} (hx : x ∈ A)
    (h : ¬IsUnit (⟨x, hx⟩ : A)) : x ∈ A.comapResidue A'' :=
  (mem_comapResidue A A'').mpr ⟨hx, by
    rw [(residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr
      (_root_.mem_nonunits_iff.mpr h))]
    exact zero_mem _⟩

theorem residue_inclusion_mem (c : A.comapResidue A'') :
    residue A (Subring.inclusion (A.comapResidue_le A'') c) ∈ A'' := by
  obtain ⟨hx, hres⟩ := (mem_comapResidue A A'').mp c.2
  rwa [show Subring.inclusion (A.comapResidue_le A'') c = ⟨(c : K), hx⟩ from
    Subtype.ext rfl]

/-- The residue map of the composite valuation ring onto the second factor: the
restriction of the residue map of `A` along the inclusion `C ⊆ A`, corestricted
to `A''`. -/
noncomputable def residueRestrict : A.comapResidue A'' →+* A''.toSubring :=
  ((residue A).comp (Subring.inclusion (A.comapResidue_le A''))).codRestrict
    A''.toSubring (A.residue_inclusion_mem A'')

/-- The residue map of the composite valuation ring onto `A''` is surjective. This is
the surjectivity half of the identification `C/𝔪' ≅ A''`. -/
theorem residueRestrict_surjective :
    Function.Surjective (A.residueRestrict A'') := by
  rintro ⟨b, hb⟩
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := A) b
  have hmem : (a : K) ∈ A.comapResidue A'' :=
    (mem_comapResidue A A'').mpr ⟨a.2, by rwa [ha]⟩
  refine ⟨⟨(a : K), hmem⟩, ?_⟩
  apply Subtype.ext
  change residue A (Subring.inclusion (A.comapResidue_le A'') ⟨(a : K), hmem⟩) = b
  rw [show Subring.inclusion (A.comapResidue_le A'') ⟨(a : K), hmem⟩ = a from
    Subtype.ext rfl, ha]

/-- The kernel of the residue map of the composite valuation ring is the trace of the
maximal ideal of `A`. Together with `residueRestrict_surjective` this is the
identification `C/𝔪' ≅ A''`. -/
theorem ker_residueRestrict :
    RingHom.ker (A.residueRestrict A'') =
      (IsLocalRing.maximalIdeal A).comap (Subring.inclusion (A.comapResidue_le A'')) := by
  ext c
  rw [RingHom.mem_ker, Ideal.mem_comap]
  constructor
  · intro h
    have h0 : residue A (Subring.inclusion (A.comapResidue_le A'') c) = 0 :=
      congrArg Subtype.val h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  · intro h
    apply Subtype.ext
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h

end ValuationSubring
