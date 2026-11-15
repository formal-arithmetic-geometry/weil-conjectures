/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.AlgebraicGeometry.ProjTwistFiniteCanonicalEval
import WeilConjectures.AlgebraicGeometry.ProjTwistFiniteValues

/-!
# Finite localization data of twist sections

## References

* Stacks Project, Tags 01MN and 01M7.
-/

@[expose] public section

universe v
open CategoryTheory Opposite LocalizedModule
namespace AlgebraicGeometry.Proj

/-- A finite principal cover carries fractions representing the section on every chart
(Stacks, Tag 01M7). -/
theorem twist_finiteLocal_representatives
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) :
    let B := HomogeneousLocalization.Away 𝒜 f
    let M := LocalizedModule.Away f A
    letI : Module B M := Module.compHom M (algebraMap B (Localization.Away f))
    ∃ (n : ℕ) (g : Fin n → B) (_ : Ideal.span (Set.range g) = ⊤)
      (t : ∀ i : Fin n, LocalizedModule.Away (g i) M),
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
        e (t i) = (s.1 p).1) := by
  dsimp
  obtain ⟨n, g, hspan, t, hv⟩ := twist_finiteLocal_values 𝒜 k f b hb hf s
  refine ⟨n, g, hspan, t, ?_⟩
  intro i p hi
  obtain ⟨e, he, hlin⟩ := twist_finiteLocal_canonical_eval 𝒜 f (g i) p hi
  refine ⟨e, he, hlin, ?_⟩
  exact hv i p e he hlin

end AlgebraicGeometry.Proj
