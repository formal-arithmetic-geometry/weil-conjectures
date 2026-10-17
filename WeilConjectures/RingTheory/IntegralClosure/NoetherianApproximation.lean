/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Noetherian normal local subrings of a normal local domain
-/

@[expose] public section

open IsLocalRing

namespace IsLocalRing

variable {A C : Type*} [CommRing A] [IsLocalRing A] [CommRing C] [IsDomain C]

/-- The image in `A` of the localization of `C` at the contraction of the maximal ideal of `A`
along an injective map `ι : C → A`. -/
theorem exists_subring_of_injective [IsNoetherianRing C] [IsIntegrallyClosed C] (ι : C →+* A)
    (hι : Function.Injective ι) :
    ∃ P : Subring A, IsNoetherianRing P ∧ IsLocalRing P ∧ IsIntegrallyClosed P ∧
      IsLocalHom P.subtype ∧
      ∀ (c s : C) (a : A), ι s ∉ maximalIdeal A → ι s * a = ι c → a ∈ P := by
  set q := (maximalIdeal A).comap ι
  let R := Localization.AtPrime q
  have hunit (s : q.primeCompl) : IsUnit (ι s) := by
    by_contra h
    exact s.2 (by simpa [q] using h)
  let φ : R →+* A := IsLocalization.lift (M := q.primeCompl) hunit
  have hle : q.primeCompl ≤ nonZeroDivisors C := q.primeCompl_le_nonZeroDivisors
  have hφ : Function.Injective φ := by
    rw [IsLocalization.lift_injective_iff]
    simp [(IsLocalization.injective R hle).eq_iff, hι.eq_iff]
  let e : R ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun x y h ↦ hφ congr($h.1), φ.rangeRestrict_surjective⟩
  have := IsLocalization.isNoetherianRing q.primeCompl R inferInstance
  refine ⟨φ.range, isNoetherianRing_of_ringEquiv R e, .of_surjective' _ e.surjective, ?_, ?_, ?_⟩
  · have := isIntegrallyClosed_of_isLocalization R q.primeCompl hle
    exact IsIntegrallyClosed.of_equiv e
  · constructor
    intro x hx
    obtain ⟨r, rfl⟩ := e.surjective x
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl r
    have hcs : ι c = ι s * φ (IsLocalization.mk' R c s) :=
      (IsLocalization.lift_mk'_spec _ _ _ _).mp rfl
    have hc : c ∉ q := by
      intro hc
      refine (mem_maximalIdeal _).mp hc ?_
      rw [hcs]
      exact (hunit s).mul hx
    exact IsUnit.map e ((IsLocalization.AtPrime.isUnit_mk'_iff R q c s).mpr hc)
  · intro c s a hs h
    exact ⟨IsLocalization.mk' R c (⟨s, hs⟩ : q.primeCompl),
      (IsLocalization.lift_mk'_spec _ _ _ _).mpr h.symm⟩


/-- Let `B → A` be an injective map from a Noetherian domain to a normal local domain such that
integral closures of `B` in finite extensions of its fraction field are finite over `B`. If every
element `e` of a finite set `E ⊆ A` is a quotient `(g e) / g` of elements integral over `B` with
`g` a unit of `A`, then `E` is contained in a Noetherian normal local subring of `A` dominated
by `A`. -/
theorem exists_subring_of_isIntegral.{v} {A : Type v} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] (B : Type*) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Algebra B A] (hB : Function.Injective (algebraMap B A))
    (hfin : ∀ (L : Type v) [Field L] [Algebra (FractionRing B) L] [Algebra B L]
      [IsScalarTower B (FractionRing B) L] [FiniteDimensional (FractionRing B) L],
      Module.Finite B (integralClosure B L))
    {E : Set A} (hE : E.Finite)
    (hg : ∀ e ∈ E, ∃ g ∉ maximalIdeal A, IsIntegral B g ∧ IsIntegral B (g * e)) :
    ∃ P : Subring A, E ⊆ P ∧ IsNoetherianRing P ∧ IsLocalRing P ∧ IsIntegrallyClosed P ∧
      IsLocalHom P.subtype := by
  classical
  choose! g hgm hgi hgei using hg
  let F := FractionRing A
  let K := FractionRing B
  have : IsScalarTower B A F := inferInstance
  have : FaithfulSMul B F := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (by rw [IsScalarTower.algebraMap_eq B A F]; exact (IsFractionRing.injective A F).comp hB)
  let : Algebra K F := FractionRing.liftAlgebra B F
  have : IsScalarTower B K F := FractionRing.isScalarTower_liftAlgebra B F
  let S : Set F := (fun e ↦ algebraMap A F (g e)) '' E ∪ (fun e ↦ algebraMap A F (g e * e)) '' E
  have hSint (x : F) (hx : x ∈ S) : IsIntegral B x := by
    rcases hx with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
    · exact (hgi e he).map (IsScalarTower.toAlgHom B A F)
    · exact (hgei e he).map (IsScalarTower.toAlgHom B A F)
  let L := IntermediateField.adjoin K S
  have : Finite S := ((hE.image _).union (hE.image _)).to_subtype
  have : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x hx ↦ (hSint x hx).tower_top
  have : IsScalarTower B L F := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply B K F x, IsScalarTower.algebraMap_apply B K L x]
    rfl
  let C := integralClosure B L
  have := hfin L
  have : IsNoetherianRing C := IsNoetherianRing.of_finite B C
  have : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  let ψ : C →+* F := (algebraMap L F).comp (algebraMap C L)
  have hψi (x : C) : IsIntegral B (ψ x) := x.2.map (IsScalarTower.toAlgHom B L F)
  have hψ (x : C) : ψ x ∈ (algebraMap A F).range :=
    IsIntegrallyClosed.isIntegral_iff.mp (hψi x).tower_top
  let eA : A ≃+* (algebraMap A F).range := RingEquiv.ofBijective (algebraMap A F).rangeRestrict
    ⟨fun x y h ↦ IsFractionRing.injective A F congr($h.1), (algebraMap A F).rangeRestrict_surjective⟩
  let ι : C →+* A := eA.symm.toRingHom.comp (ψ.codRestrict _ hψ)
  have hιF (x : C) : algebraMap A F (ι x) = ψ x := congr($(eA.apply_symm_apply ⟨ψ x, hψ x⟩).1)
  have hι : Function.Injective ι := fun x y h ↦ by
    have := congr(algebraMap A F $h)
    rw [hιF, hιF] at this
    exact Subtype.ext ((algebraMap L F).injective this)
  obtain ⟨P, hPn, hPl, hPi, hPh, hP⟩ := exists_subring_of_injective ι hι
  refine ⟨P, fun e he ↦ ?_, hPn, hPl, hPi, hPh⟩
  have hmem (a : A) (ha : algebraMap A F a ∈ S) : ∃ c : C, ι c = a := by
    have : IsIntegral B (⟨algebraMap A F a, IntermediateField.subset_adjoin K S ha⟩ : L) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom B L F) (algebraMap L F).injective).mp
        (hSint _ ha)
    exact ⟨⟨_, this⟩, IsFractionRing.injective A F (hιF _)⟩
  obtain ⟨s, hs⟩ := hmem (g e) (Or.inl ⟨e, he, rfl⟩)
  obtain ⟨c, hc⟩ := hmem (g e * e) (Or.inr ⟨e, he, rfl⟩)
  exact hP c s e (hs ▸ hgm e he) (by rw [hs, hc])

end IsLocalRing
