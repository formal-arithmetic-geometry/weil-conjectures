/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Sheaf.RingTheory.MapIntoHenselianColimit
import WeilConjectures.SixFunctors.ProEtale.GenericPoint
import Mathlib.RingTheory.Localization.Algebra

/-! # Sections of separably generated residue fields

Source: Stacks Project, Tags 04GG, 06RR, 08HQ and 08HR; the coefficient-field argument
in blueprint thm-sc-affine-torsion-cd.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace Algebra

private theorem lift_separable_field
    (L E R : Type u) [Field L] [Field E] [CommRing R] [HenselianLocalRing R]
    [Algebra L E] [Algebra L R] [Algebra.IsSeparable L E]
    (ρ : R →ₐ[L] E) (hsurj : Function.Surjective ρ)
    (hker : RingHom.ker ρ.toRingHom = IsLocalRing.maximalIdeal R) :
    ∃ j : E →ₐ[L] R, ρ.comp j = AlgHom.id L E := by
  classical
  let m := IsLocalRing.maximalIdeal R
  let q : Ideal E := ⊥
  let p : Ideal L := ⊥
  have units : m.primeCompl ≤ (IsUnit.submonoid E).comap ρ.toRingHom := by
    intro x hx
    change IsUnit (ρ x)
    rw [isUnit_iff_ne_zero]
    intro he
    apply hx
    change x ∈ IsLocalRing.maximalIdeal R
    rw [← hker]
    exact he
  let ψ : m.ResidueField →+* E :=
    Ideal.ResidueField.lift m ρ.toRingHom hker.ge units
  have hψ (r : R) : ψ (algebraMap R m.ResidueField r) = ρ r :=
    Ideal.ResidueField.lift_algebraMap ..
  have hψsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨r, rfl⟩ := hsurj x
    exact ⟨algebraMap R m.ResidueField r, hψ r⟩
  let e : m.ResidueField ≃+* E := RingEquiv.ofBijective ψ ⟨ψ.injective, hψsurj⟩
  let eE : E ≃+* q.ResidueField := RingEquiv.ofBijective (algebraMap E q.ResidueField)
    ⟨(algebraMap E q.ResidueField).injective, q.algebraMap_residueField_surjective⟩
  let τ : q.ResidueField →+* m.ResidueField := e.symm.toRingHom.comp eE.symm.toRingHom
  have hp : p = q.comap (algebraMap L E) := by
    ext x
    change x = 0 ↔ algebraMap L E x = 0
    simp
  have hm : p = m.comap (algebraMap L R) := by
    ext x
    change x = 0 ↔ algebraMap L R x ∈ IsLocalRing.maximalIdeal R
    rw [← hker]
    change x = 0 ↔ ρ (algebraMap L R x) = 0
    rw [ρ.commutes, map_eq_zero]
  have hτ : τ.comp (Ideal.ResidueField.map p q (algebraMap L E) hp) =
      Ideal.ResidueField.map p m (algebraMap L R) hm := by
    apply Ideal.ResidueField.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
    apply e.injective
    change e (e.symm (eE.symm (algebraMap E q.ResidueField (algebraMap L E x)))) = _
    rw [e.apply_symm_apply]
    change eE.symm (eE (algebraMap L E x)) = ψ (algebraMap R m.ResidueField
      (algebraMap L R x))
    rw [eE.symm_apply_apply, hψ, ρ.commutes]
  let : IndEtale L E := IndEtale.of_isSeparable L E
  obtain ⟨I, hcat, hfilt, P, hP⟩ := IndEtale.exists_colimitPresentation (R := L) (S := E)
  let := hcat
  let := hfilt
  let := P.hasColimit
  obtain ⟨j, ⟨hj, hres⟩, -⟩ := map_into_henselian_colimit L R E I P.diag
    ⟨(colimit.isColimit P.diag).coconePointUniqueUpToIso P.isColimit⟩ hP q p hp hm τ hτ
  refine ⟨j, ?_⟩
  ext x
  have hh := Ideal.ResidueField.map_algebraMap q m j.toRingHom hj x
  rw [hres] at hh
  have hh' := congrArg e hh
  change e (τ (eE x)) = ψ (algebraMap R m.ResidueField (j x)) at hh'
  rw [hψ] at hh'
  change e (e.symm (eE.symm (eE x))) = ρ (j x) at hh'
  rw [e.apply_symm_apply, eE.symm_apply_apply] at hh'
  exact hh'.symm

/-- A separably generated residue field has a coefficient section over its base field.
Source: blueprint thm-sc-affine-torsion-cd, local calculation in dimension d;
Stacks Tags 04GG, 06RR, 08HQ and 08HR.
(blueprint: new-lem-sc-henselian-separably-generated-residue-section)

Proof: lift the separating family through the surjection.  Every nonzero
polynomial in the lifts has nonzero residue and is a unit.  Localization thus
embeds the rational-function field in R compatibly with reduction.  The residue
extension over this field is separable algebraic, hence ind-etale.  Apply unique
henselian lifting at its finite etale stages; uniqueness makes the lifts
compatible, so the colimit gives a section on the entire residue field.  The
empty separating family uses the same polynomial-localization argument.
-/
theorem exists_section_of_separating_family
    (K E R : Type u) [Field K] [Field E] [CommRing R] [HenselianLocalRing R]
    [Algebra K E] [Algebra K R]
    (ρ : R →ₐ[K] E) (hsurj : Function.Surjective ρ)
    (hker : RingHom.ker ρ.toRingHom = IsLocalRing.maximalIdeal R)
    (ι : Type u) (v : ι → E) (hv : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) E] :
    ∃ j : E →ₐ[K] R, ρ.comp j = AlgHom.id K E := by
  classical
  choose u hu using fun i ↦ hsurj (v i)
  let ev : MvPolynomial ι K →ₐ[K] R := MvPolynomial.aeval u
  have hev : ρ.comp ev = MvPolynomial.aeval v := by
    ext i
    simpa [ev] using hu i
  have hunits (p : nonZeroDivisors (MvPolynomial ι K)) : IsUnit (ev p) := by
    by_contra hn
    have hm : ev p ∈ IsLocalRing.maximalIdeal R := by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hn
    have hz : ρ (ev p) = 0 := by
      change ev p ∈ RingHom.ker ρ.toRingHom
      rw [hker]
      exact hm
    have hp : MvPolynomial.aeval v (p : MvPolynomial ι K) = 0 := by
      rw [← hev]
      exact hz
    exact (mem_nonZeroDivisors_iff_ne_zero.mp p.property)
      ((algebraicIndependent_iff_injective_aeval.mp hv) (by simpa using hp))
  let T := FractionRing (MvPolynomial ι K)
  let φ : T →ₐ[K] R := IsLocalization.liftAlgHom hunits
  let L := IntermediateField.adjoin K (Set.range v)
  let jL : L →ₐ[K] R := φ.comp hv.aevalEquivField.symm.toAlgHom
  have hrφ : ρ.comp φ = (IntermediateField.val L).comp hv.aevalEquivField.toAlgHom := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial ι K))
    apply RingHom.ext
    intro p
    change ρ (φ (algebraMap (MvPolynomial ι K) T p)) =
      (hv.aevalEquivField (algebraMap (MvPolynomial ι K) T p) : E)
    change ρ (IsLocalization.lift hunits (algebraMap (MvPolynomial ι K) T p)) = _
    rw [IsLocalization.lift_eq]
    exact (DFunLike.congr_fun hev p).trans
      (hv.aevalEquivField_algebraMap_apply_coe p).symm
  have hrL (x : L) : ρ (jL x) = (x : E) := by
    have hx := DFunLike.congr_fun hrφ (hv.aevalEquivField.symm x)
    change ρ (jL x) = (hv.aevalEquivField (hv.aevalEquivField.symm x) : E) at hx
    simpa only [AlgEquiv.apply_symm_apply] using hx
  let : Algebra L R := jL.toRingHom.toAlgebra
  let : IsScalarTower K L R := IsScalarTower.of_algebraMap_eq fun c ↦ (jL.commutes c).symm
  let ρL : R →ₐ[L] E :=
    { ρ.toRingHom with commutes' x := hrL x }
  obtain ⟨j, hj⟩ := lift_separable_field L E R ρL hsurj hker
  refine ⟨j.restrictScalars K, ?_⟩
  ext x
  exact DFunLike.congr_fun hj x

end Algebra
