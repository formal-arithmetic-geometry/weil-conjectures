/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.StrictlyStandardElement
public import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.StrictlyStandardLocalizedConormalSplit
import WeilConjectures.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
# Smooth localization at a strictly standard element

The localization of a finitely presented algebra at a strictly standard element is smooth
(`Algebra.smooth_localizationAway_of_isStrictlyStandardElement`).

## Implementation details

After localizing at `a`, the conormal map of the given presentation has a left inverse
(`strictlyStandard_localized_conormal_split`). Adjoining a variable `y` with relation `hy - 1`,
for a lift `h` of `a`, presents `A_a`; its differential is the direct sum of the localized
conormal differential and multiplication by `a`. Combining the two left inverses splits the
conormal map of this presentation, which gives smoothness.

## References

* [Stacks, Tag 07CA], first paragraph of the proof
-/

@[expose] public section

universe u v

namespace Algebra

/-- Localization at a strictly standard element of a finitely presented algebra is smooth. -/
theorem smooth_localizationAway_of_isStrictlyStandardElement
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [FinitePresentation R A] (a : A) (ha : IsStrictlyStandardElement (R := R) a) :
    Smooth R (Localization.Away a) := by
  classical
  obtain ⟨n, m, c, P, hc, a', hminor, hrelations⟩ := ha
  let S := Localization.Away a
  let G := P.toGenerators
  let Q := (Generators.localizationAway S a).comp G
  obtain ⟨l, hl⟩ := P.strictlyStandard_localized_conormal_split hc a a' hminor hrelations
  have hf : algebraMap G.Ring A (G.σ a) = a := G.toExtension.algebraMap_σ a
  obtain ⟨_, _, r, _, e1, e2, e0, _, _, _, hcomm, _, _⟩ :=
    G.principal_localization_naive_cotangent a (G.σ a) hf (Bg := S)
  obtain ⟨unit, hunit⟩ := IsLocalization.Away.algebraMap_isUnit (S := S) a
  let inv : S →ₗ[S] S := (↑unit⁻¹ : S) • LinearMap.id
  let left := e1.symm.toLinearMap.comp ((l.prodMap inv).comp e0.toLinearMap)
  have hleft : left.comp Q.toExtension.cotangentComplex = LinearMap.id := by
    ext x
    obtain ⟨⟨y, z⟩, rfl⟩ := e1.symm.surjective x
    change e1.symm (l (e0 (Q.toExtension.cotangentComplex
      (e1.symm (y, z)))).1, inv (e0 (Q.toExtension.cotangentComplex
      (e1.symm (y, z)))).2) = e1.symm (y, z)
    rw [hcomm, e0.apply_symm_apply]
    congr 1
    apply Prod.ext
    · exact DFunLike.congr_fun hl y
    · change (↑unit⁻¹ : S) * (algebraMap A S a * z) = z
      rw [← hunit, ← mul_assoc, Units.inv_mul, one_mul]
  have : FormallySmooth R Q.toExtension.Ring := by
    change FormallySmooth R (MvPolynomial _ R)
    infer_instance
  have : FormallySmooth R S :=
    Q.toExtension.formallySmooth_iff_split_injection.mpr ⟨left, hleft⟩
  exact ⟨inferInstance, inferInstance⟩

end Algebra
