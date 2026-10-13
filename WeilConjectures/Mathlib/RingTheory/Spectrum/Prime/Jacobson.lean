/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Isolated points of the spectrum of a finite type algebra over a field

## Main statements

- `PrimeSpectrum.isMaximal_and_finite_residueField_of_isOpen_singleton`: an isolated point of
  `Spec B`, for `B` of finite type over a field `k`, is a closed point with residue field finite
  over `k`.
- `PrimeSpectrum.finite_setOf_isOpen_singleton`: `Spec B` has only finitely many isolated points.
-/

@[expose] public section

namespace PrimeSpectrum

/-- Let `B` be a finite type algebra over a field `k`. If `{𝔭}` is open in `Spec B`, then `𝔭` is
a maximal ideal and its residue field `κ(𝔭)` is finite over `k`
(blueprint: `lem-weil-pbc-isolated-prime-finite-type-algebra-residue-finite`). -/
theorem isMaximal_and_finite_residueField_of_isOpen_singleton (k : Type*) {B : Type*} [Field k]
    [CommRing B] [Algebra k B] [Algebra.FiniteType k B] {𝔭 : PrimeSpectrum B}
    (h : IsOpen {𝔭}) :
    𝔭.asIdeal.IsMaximal ∧ Module.Finite k 𝔭.asIdeal.ResidueField := by
  have : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hmax : 𝔭.asIdeal.IsMaximal := by
    rw [← isClosed_singleton_iff_isMaximal]
    exact IsClopen.isClosed
      (((isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing 𝔭).out 0 1).mp h)
  refine ⟨hmax, ?_⟩
  let _ : Field (B ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  have : Module.Finite k (B ⧸ 𝔭.asIdeal) := finite_of_finite_type_of_isJacobsonRing k _
  let e : (B ⧸ 𝔭.asIdeal) ≃ₐ[k] 𝔭.asIdeal.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom k _ _)
      (Ideal.bijective_algebraMap_quotient_residueField 𝔭.asIdeal)
  exact Module.Finite.equiv e.toLinearEquiv

/-- Let `B` be a finite type algebra over a field `k`. Then `Spec B` has only finitely many
isolated points, i.e. points `𝔮` with `{𝔮}` open
(blueprint: `lem-weil-pbc-finite-type-field-finite-isolated-points`). -/
theorem finite_setOf_isOpen_singleton (k : Type*) (B : Type*) [Field k] [CommRing B]
    [Algebra k B] [Algebra.FiniteType k B] :
    {𝔮 : PrimeSpectrum B | IsOpen {𝔮}}.Finite := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  refine (finite_setOfPred_isMin B).subset fun 𝔮 h𝔮 ↦ ?_
  have := IsOpen.stableUnderGeneralization (s := {𝔮}) h𝔮
  rw [stableUnderGeneralization_singleton, ← isMin_iff] at this
  exact this

end PrimeSpectrum
