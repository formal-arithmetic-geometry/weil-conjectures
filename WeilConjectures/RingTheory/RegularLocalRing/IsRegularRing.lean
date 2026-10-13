/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import WeilConjectures.Mathlib.RingTheory.Regular.ProjectiveDimension
public import WeilConjectures.RingTheory.RegularLocalRing.UniqueFactorization

/-!
# Localizations of regular local rings are regular

Let `R` be a regular local ring and `p` a prime of `R`. The `R`-module `R ⧸ p` has finite projective
dimension (`IsRegularLocalRing.exists_hasProjectiveDimensionLE`), hence so has its localization
`κ(p)` over `R_p`; by Serre's theorem
(`IsRegularLocalRing.of_hasProjectiveDimensionLE_residueField`)
`R_p` is regular [Stacks 00OE]. Hence a regular local ring is a regular ring
(`IsRegularLocalRing.isRegularRing`), a unique factorization domain
(`IsRegularLocalRing.uniqueFactorizationMonoid'`) and in particular integrally closed.

These are inputs of the Zariski–Nagata purity theorem [Stacks 0BMA], used for blueprint
`sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

universe u

open IsLocalRing CategoryTheory

variable {R : Type u} [CommRing R]

namespace Ideal

/-- The map `R ⧸ p → κ(p)` is a localization at `R \ p` as `R`-modules. -/
instance isLocalizedModule_quotient_residueField (p : Ideal R) [p.IsPrime] :
    IsLocalizedModule p.primeCompl
      (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField).toLinearMap := by
  rw [isLocalizedModule_iff_isLocalization]
  have : Algebra.algebraMapSubmonoid (R ⧸ p) p.primeCompl = nonZeroDivisors (R ⧸ p) := by
    ext z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [mem_nonZeroDivisors_iff_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · rintro ⟨b, hb, hbz⟩ ha
      apply hb
      have : Ideal.Quotient.mk p b = Ideal.Quotient.mk p a := hbz
      rw [Ideal.Quotient.eq] at this
      simpa using p.add_mem this ha
    · intro ha
      exact ⟨a, ha, rfl⟩
  rw [this]
  infer_instance

end Ideal

namespace IsRegularLocalRing

/-- **Localizations of regular local rings are regular** [Stacks 00OE]. -/
theorem isRegularLocalRing_localization [IsRegularLocalRing R] (p : Ideal R) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  obtain ⟨n, hn⟩ := exists_hasProjectiveDimensionLE.{u} (ModuleCat.of.{u} R (R ⧸ p))
  have h1 := ModuleCat.localizedModule_hasProjectiveDimensionLE n p.primeCompl
    (ModuleCat.of.{u} R (R ⧸ p))
  let M := (ModuleCat.of.{u} R (R ⧸ p)).localizedModule p.primeCompl
  have := ModuleCat.localizedModule_isLocalizedModule (ModuleCat.of.{u} R (R ⧸ p)) p.primeCompl
  let e₀ : M ≃ₗ[R] p.ResidueField := IsLocalizedModule.linearEquiv p.primeCompl
    ((ModuleCat.of.{u} R (R ⧸ p)).localizedModuleMkLinearMap p.primeCompl)
    (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField).toLinearMap
  let e : M ≃ₗ[Localization.AtPrime p] p.ResidueField :=
    e₀.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)
  exact of_hasProjectiveDimensionLE_residueField n
    (hasProjectiveDimensionLT_of_iso e.toModuleIso (n + 1))

/-- A regular local ring is a regular ring. -/
theorem isRegularRing [IsRegularLocalRing R] : IsRegularRing R where
  isRegularLocalRing_localization p _ := isRegularLocalRing_localization p

/-- **Auslander–Buchsbaum theorem**: a regular local ring is a UFD [Stacks 0AG0]. -/
theorem uniqueFactorizationMonoid' [IsRegularLocalRing R] : UniqueFactorizationMonoid R :=
  have := isRegularRing (R := R)
  uniqueFactorizationMonoid R

/-- A regular local ring is integrally closed (it is a UFD). -/
instance toIsIntegrallyClosed [IsRegularLocalRing R] : IsIntegrallyClosed R :=
  have := uniqueFactorizationMonoid' (R := R)
  inferInstance

end IsRegularLocalRing
