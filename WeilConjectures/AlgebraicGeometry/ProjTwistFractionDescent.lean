/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.Algebra.Module.DegreeZeroFractions
import WeilConjectures.AlgebraicGeometry.ProjTwistFiniteLocalizationData
import WeilConjectures.RingTheory.CoverModuleExact
import WeilConjectures.AlgebraicGeometry.ProjTwistDegreeDetection

/-!
# Descent of locally homogeneous fractions on a Proj basic open

## References

* Stacks Project, Tags 01MN and 01M7.
-/

@[expose] public section

universe v
open CategoryTheory Opposite LocalizedModule
namespace AlgebraicGeometry.Proj

/-- A twist section on a positive-degree basic open descends to a homogeneous fraction
(Stacks, Tags 01MN, 01M7). -/
theorem twist_fraction_descent
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) :
    ∃ z : LocalizedModule.Away f A,
      z ∈ degreeZeroFractions (fun n : ℕ ↦ (𝒜 n : Set A))
        (fun n : ℕ ↦ {y : A | if 0 ≤ k + n then y ∈ 𝒜 (k + n).toNat else y = 0})
        (Submonoid.powers f) ∧
      ∀ p : basicOpen 𝒜 f,
        IsLocalization.map (M := Submonoid.powers f)
          (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
          (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
          (Submonoid.powers_le.mpr p.2) z = (s.1 p).1 := by
  let B := HomogeneousLocalization.Away 𝒜 f
  let M := LocalizedModule.Away f A
  let : Module B M := Module.compHom M (algebraMap B (Localization.Away f))
  obtain ⟨n, g, hspan, t, ht, heval⟩ := twist_finiteLocalization_data 𝒜 k f b hb hf s
  obtain ⟨z, hz, _⟩ := (RingTheory.coverModuleExact (M := M) n g hspan).2 t ht
  have hvalue (p : basicOpen 𝒜 f) :
      IsLocalization.map (M := Submonoid.powers f)
        (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
        (Submonoid.powers_le.mpr p.2) z = (s.1 p).1 := by
    obtain ⟨i, e, he, hs⟩ := heval p
    exact (he z).symm.trans ((congrArg e (hz i)).trans hs)
  refine ⟨z, twist_degree_detection 𝒜 k f b hb hf z ?_, hvalue⟩
  intro p
  rw [hvalue p]
  exact (s.1 p).2

end AlgebraicGeometry.Proj
