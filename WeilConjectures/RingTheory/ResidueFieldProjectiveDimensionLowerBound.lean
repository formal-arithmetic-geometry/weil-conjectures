/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import WeilConjectures.Mathlib.RingTheory.Regular.ProjectiveDimension

/-!
# Embedding dimension bounds the length of a residue-field resolution

In a Noetherian local ring, the dimension of `m/m²` is bounded by the length of any projective
resolution of the residue field.

## Implementation details

The proof uses Serre's theorem that a Noetherian local ring whose residue field has finite
projective dimension is regular, and the formula for the projective dimension of the residue
field of a regular local ring, both from
`WeilConjectures.Mathlib.RingTheory.Regular.ProjectiveDimension`.

## References

* [Stacks, Tag 00OA]
* [Stacks, Tag 00OC]
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- In a Noetherian local ring, every projective resolution of the residue field of length
at most `d` satisfies `dim (m/m²) ≤ d`. -/
theorem finrank_cotangentSpace_le_of_hasProjectiveResolutionLE
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (d : ℕ)
    (h : ModuleCat.HasProjectiveResolutionLE (ModuleCat.of R (ResidueField R)) d) :
    Module.finrank (ResidueField R) (CotangentSpace R) ≤ d := by
  obtain ⟨P, hP⟩ := h
  have hdim : CategoryTheory.HasProjectiveDimensionLE
      (ModuleCat.of R (ResidueField R)) d := by
    refine CategoryTheory.HasProjectiveDimensionLT.mk ?_
    intro i hi Y e
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (i + 1) rfl
    have hf0 : f = 0 := (hP i (by omega)).eq_of_src f 0
    subst f
    simp
  have : IsRegularLocalRing R :=
    IsRegularLocalRing.of_hasProjectiveDimensionLE_residueField d hdim
  have hle := (CategoryTheory.projectiveDimension_le_iff
    (ModuleCat.of R (ResidueField R)) d).mpr hdim
  let e : ResidueField R ≃ₗ[R] Shrink.{u} (R ⧸ maximalIdeal R) :=
    (Shrink.linearEquiv R _).symm
  rw [CategoryTheory.projectiveDimension_eq_of_iso e.toModuleIso,
    IsRegularLocalRing.projectiveDimension_quotient_maximalIdeal,
    spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at hle
  exact_mod_cast hle

end IsLocalRing
