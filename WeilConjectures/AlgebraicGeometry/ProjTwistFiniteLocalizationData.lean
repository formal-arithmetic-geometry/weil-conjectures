/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.RingTheory.CoverModuleExact

import WeilConjectures.AlgebraicGeometry.ProjTwistFiniteLocalRepresentatives
import WeilConjectures.AlgebraicGeometry.ProjTwistLocalOverlapCompatibility

import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Finite localization data of twist sections

## References

* Stacks Project, Tags 01MN and 01M7.
-/

@[expose] public section

universe v
open CategoryTheory Opposite LocalizedModule
namespace AlgebraicGeometry.Proj

/-- A family spanning the unit ideal has a unit image in any local ring. -/
private theorem exists_unit_of_span_top
    {B R ι : Type*} [CommRing B] [CommRing R] [IsLocalRing R]
    (g : ι → B) (hspan : Ideal.span (Set.range g) = ⊤) (F : B →+* R) :
    ∃ i, IsUnit (F (g i)) := by
  classical
  by_contra hn
  have hle : Ideal.span (Set.range g) ≤ Ideal.comap F (IsLocalRing.maximalIdeal R) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change F (g i) ∈ IsLocalRing.maximalIdeal R
    exact (IsLocalRing.mem_maximalIdeal _).mpr (fun h ↦ hn ⟨i, h⟩)
  have h1 := hle (hspan.symm ▸ (show (1 : B) ∈ (⊤ : Ideal B) from trivial))
  change F 1 ∈ IsLocalRing.maximalIdeal R at h1
  exact h1 (by simp)

/-- A twist section has compatible ordinary fractions on a finite principal cover of
Spec(A_(f)), with evaluations agreeing with the original section (Stacks, Tag 01M7). -/
theorem twist_finiteLocalization_data
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) :
    let B := HomogeneousLocalization.Away 𝒜 f
    let M := LocalizedModule.Away f A
    letI : Module B M := Module.compHom M (algebraMap B (Localization.Away f))
    ∃ (n : ℕ) (g : Fin n → B) (_ : Ideal.span (Set.range g) = ⊤),
      let ρ := fun (a h : B) (ha : a ∣ h) ↦
        IsLocalizedModule.lift (Submonoid.powers a)
          (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
          (LocalizedModule.mkLinearMap (Submonoid.powers h) M)
          (RingTheory.localizationAway_map_units_of_dvd (M := M) a h ha)
      ∃ t : ∀ i : Fin n, LocalizedModule.Away (g i) M,
        (∀ i j : Fin n,
          ρ (g i) (g i * g j) (dvd_mul_right (g i) (g j)) (t i) =
            ρ (g j) (g i * g j) (dvd_mul_left (g j) (g i)) (t j)) ∧
        ∀ p : basicOpen 𝒜 f,
          ∃ (i : Fin n)
            (e : LocalizedModule.Away (g i) M →+
              Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal),
            (∀ z : M,
              e (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) M z) =
                IsLocalization.map (M := Submonoid.powers f)
                  (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
                  (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
                  (Submonoid.powers_le.mpr p.2) z) ∧
            e (t i) = (s.1 p).1  := by
  rcases twist_finiteLocal_representatives 𝒜 k f b hb hf s with
    ⟨n, g, hspan, t, hlocal⟩
  refine ⟨n, g, hspan, t, ?_, ?_⟩
  · exact twist_localOverlap_compatibility 𝒜 k f b hb hf s n g t hlocal
  · intro p
    let F := IsLocalization.map (M := Submonoid.powers f)
      (S := LocalizedModule.Away f A)
      (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
      (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
      (Submonoid.powers_le.mpr p.2)
    obtain ⟨i, hi⟩ := exists_unit_of_span_top g hspan
      (F.comp (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f)))
    obtain ⟨e, he, _, hs⟩ := hlocal i p hi
    exact ⟨i, e, he, hs⟩

end AlgebraicGeometry.Proj
