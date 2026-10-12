/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import Sheaf.RingTheory.CoverModuleExact

import Sheaf.AlgebraicGeometry.ProjBasicOpenLocalizationDetection

/-!
# Finite localization data of twist sections

Source: Stacks Project, Tags 01MN and 01M7.
-/

@[expose] public section

universe v
open CategoryTheory Opposite LocalizedModule
namespace AlgebraicGeometry.Proj

/-- Pointwise overlap equality for two fixed chart indices.
Source: Stacks Project, Tag 01M7, the local fraction comparison on a basic overlap.
(blueprint: lem-sc-proj-twist-local-overlap-pointwise)

This is the local algebraic comparison at one homogeneous prime. Its proof uses the
additive and scalar-compatible evaluations supplied for the two representatives and
identifies both with the common section value. -/
theorem twist_localOverlap_pointwise
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f)))
    (n : ℕ) (g : Fin n → HomogeneousLocalization.Away 𝒜 f)
    (t : ∀ i : Fin n, LocalizedModule.Away (g i)
      (LocalizedModule.Away f A))
    (hlocal : ∀ (i : Fin n) (p : basicOpen 𝒜 f),
      let F := IsLocalization.map (M := Submonoid.powers f)
        (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
        (Submonoid.powers_le.mpr p.2)
      IsUnit (F (algebraMap (HomogeneousLocalization.Away 𝒜 f)
        (LocalizedModule.Away f A) (g i))) →
      ∃ e : LocalizedModule.Away (g i) (LocalizedModule.Away f A) →+
          Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal,
        (∀ z : LocalizedModule.Away f A,
          e (LocalizedModule.mkLinearMap (Submonoid.powers (g i))
            (LocalizedModule.Away f A) z) = F z) ∧
        (∀ (a : HomogeneousLocalization.Away 𝒜 f)
          (x : LocalizedModule.Away (g i) (LocalizedModule.Away f A)),
          e (a • x) = F (algebraMap (HomogeneousLocalization.Away 𝒜 f)
            (LocalizedModule.Away f A) a) * e x) ∧
        e (t i) = (s.1 p).1)
    (i j : Fin n) :
      let ρ := fun (a h : HomogeneousLocalization.Away 𝒜 f) (ha : a ∣ h) ↦
        IsLocalizedModule.lift (Submonoid.powers a)
          (LocalizedModule.mkLinearMap (Submonoid.powers a)
            (LocalizedModule.Away f A))
          (LocalizedModule.mkLinearMap (Submonoid.powers h)
            (LocalizedModule.Away f A))
          (RingTheory.localizationAway_map_units_of_dvd
            (M := LocalizedModule.Away f A) a h ha)
      ρ (g i) (g i * g j) (dvd_mul_right (g i) (g j)) (t i) =
        ρ (g j) (g i * g j) (dvd_mul_left (g j) (g i)) (t j) := by
  sorry

theorem twist_localOverlap_compatibility
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) :
    let B := HomogeneousLocalization.Away 𝒜 f
    let M := LocalizedModule.Away f A
    letI : Module B M := Module.compHom M (algebraMap B (Localization.Away f))
    ∀ (n : ℕ) (g : Fin n → B) (t : ∀ i : Fin n, LocalizedModule.Away (g i) M),
      (∀ (i : Fin n) (p : basicOpen 𝒜 f),
      let F := IsLocalization.map (M := Submonoid.powers f)
        (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
        (Submonoid.powers_le.mpr p.2)
      IsUnit (F (algebraMap B (Localization.Away f) (g i))) →
      ∃ e : LocalizedModule.Away (g i) M →+
          Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal,
        (∀ z : M, e (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) M z) = F z) ∧
        (∀ (a : B) (x : LocalizedModule.Away (g i) M),
          e (a • x) = F (algebraMap B (Localization.Away f) a) * e x) ∧
        e (t i) = (s.1 p).1) →
      let ρ := fun (a h : B) (ha : a ∣ h) ↦
        IsLocalizedModule.lift (Submonoid.powers a)
          (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
          (LocalizedModule.mkLinearMap (Submonoid.powers h) M)
          (RingTheory.localizationAway_map_units_of_dvd (M := M) a h ha)
      ∀ i j : Fin n,
        ρ (g i) (g i * g j) (dvd_mul_right (g i) (g j)) (t i) =
          ρ (g j) (g i * g j) (dvd_mul_left (g j) (g i)) (t j) := by
  dsimp
  intro n g t hlocal i j
  exact twist_localOverlap_pointwise 𝒜 k f b hb hf s n g t hlocal i j

end AlgebraicGeometry.Proj
