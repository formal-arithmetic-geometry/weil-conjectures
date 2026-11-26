/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.CharP.Defs
import WeilConjectures.RingTheory.CohenRingsExist
import WeilConjectures.RingTheory.CoefficientResidueSection
import WeilConjectures.RingTheory.CohenRingLiftToCompleteLocal
import WeilConjectures.RingTheory.CoefficientSubringOfPrincipalSource

/-!
# Existence of a coefficient subring

A complete local ring `R` whose residue field has characteristic `p` contains a coefficient
subring: a complete local subring `Λ` with maximal ideal `m ∩ Λ = (p)` mapping isomorphically
onto the residue field of `R`.

## Implementation details

In residue characteristic zero the identity of the residue field is lifted successively through
the square-zero kernels of `R/mⁿ → R/mⁿ⁻¹` using formal smoothness over `ℚ`, and the lifts are
passed to the inverse limit. In positive characteristic a Cohen ring with the prescribed residue
field is mapped to `R` by lifting modulo `pⁿ` and using completeness of `R`; the kernel of this
map is zero or `(p^N)`, and in both cases the image is complete with maximal ideal `(p)`.

## References

* [Stacks, Tag 0326]
* [Stacks, Tag 032A], part (1)
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- A complete local ring whose residue field has characteristic `p` contains a coefficient
subring: a complete local subring `Λ` whose maximal ideal is `m ∩ Λ = (p)` and whose residue
field maps bijectively onto that of `R`. -/
theorem exists_coefficient_subring (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (p : ℕ) [CharP (ResidueField R) p] :
    ∃ (Λ : Subring R) (hΛ : IsLocalRing Λ),
      letI : IsLocalRing Λ := hΛ
      maximalIdeal Λ = (maximalIdeal R).comap Λ.subtype ∧
      IsAdicComplete ((maximalIdeal R).comap Λ.subtype) Λ ∧
      Function.Bijective
        (Ideal.quotientMap (I := (maximalIdeal R).comap Λ.subtype)
          (maximalIdeal R) Λ.subtype le_rfl) ∧
      (maximalIdeal R).comap Λ.subtype = Ideal.span {(p : Λ)} := by
  rcases CharP.char_is_prime_or_zero (ResidueField R) p with hp | hp
  · obtain ⟨C, hcomm, hC, ⟨e⟩⟩ := exists_cohenRing p hp (ResidueField R)
    let _ := hcomm
    obtain ⟨f, hf⟩ := exists_cohenRing_lift R p C hC e
    obtain ⟨_, hdom, hdvr, hm, hcomplete⟩ := hC
    let _ := hdom
    let _ := hdvr
    have : IsAdicComplete (maximalIdeal C) C := hm.symm ▸ hcomplete
    have hlocal : (maximalIdeal R).comap f = maximalIdeal C := by
      ext x
      rw [Ideal.mem_comap, ← residue_eq_zero_iff, ← RingHom.comp_apply, hf]
      simp [hm, Ideal.Quotient.eq_zero_iff_mem]
    have hsurj : Function.Surjective ((residue R).comp f) := by
      rw [hf]
      exact e.surjective.comp (Ideal.Quotient.mk_surjective)
    obtain ⟨hL, hprops⟩ := coefficient_subring_of_principal_source R C p hm f hlocal hsurj
    exact ⟨f.range, hL, hprops⟩
  · subst p
    obtain ⟨f, hf⟩ := exists_residue_section R
    have hm : maximalIdeal (ResidueField R) = Ideal.span {(0 : ResidueField R)} := by
      simp [maximalIdeal_eq_bot]
    have : IsAdicComplete (maximalIdeal (ResidueField R)) (ResidueField R) := by
      rw [maximalIdeal_eq_bot]
      exact IsAdicComplete.bot _
    have hlocal : (maximalIdeal R).comap f = maximalIdeal (ResidueField R) := by
      ext x
      rw [Ideal.mem_comap, ← residue_eq_zero_iff, ← RingHom.comp_apply, hf]
      simp [maximalIdeal_eq_bot]
    have hsurj : Function.Surjective ((residue R).comp f) := by
      rw [hf]
      exact Function.surjective_id
    obtain ⟨hL, hprops⟩ :=
      coefficient_subring_of_principal_source R (ResidueField R) 0
        (by simpa using hm) f hlocal hsurj
    exact ⟨f.range, hL, hprops⟩

end IsLocalRing
