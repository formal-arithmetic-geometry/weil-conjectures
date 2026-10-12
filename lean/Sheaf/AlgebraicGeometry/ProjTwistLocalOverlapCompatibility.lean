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

/-- Fractions representing one section at every chart point agree on overlaps.
Source: Stacks Project, Tag 01M7, injectivity and local fraction argument.
(blueprint: lem-sc-proj-twist-local-overlap-compatibility)

Proof: fix two chart elements. Write each as a homogeneous degree-zero fraction over a
power of f. Their product corresponds to a homogeneous positive-degree basic open
inside D₊(f). The iterated module localization is the ordinary localization at the
product of f and these homogeneous numerators, by the universal properties of ring and
module localization. At every homogeneous prime of this basic open, both chart elements
are units. The assumed linear evaluations extend uniquely to the overlap: linearity and
agreement on M force equality with the canonical ordinary localization evaluation.
The two overlap elements therefore have the same value s(p) at every such prime.
Homogeneous-prime localization detection on that basic open makes the elements equal.
If the basic open is empty the corresponding localization is zero, so equality still
holds. Zero chart elements cause no problem for the same reason. No spanning condition
or existence of a finite cover is used in this argument. -/
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
          ρ (g j) (g i * g j) (dvd_mul_left (g j) (g i)) (t j) := by sorry

end AlgebraicGeometry.Proj
