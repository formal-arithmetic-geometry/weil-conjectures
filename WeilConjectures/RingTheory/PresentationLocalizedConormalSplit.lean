/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent

/-! # Localized conormal complement of a finite polynomial presentation

For a finite presentation of `A` over `R` with `n` variables and `A_a` smooth over `R`, the
localized conormal module and `Ω[A_a/R]` together are isomorphic to `A_a^n`.

## References

* [Stacks Project, Tag 07CE](https://stacks.math.columbia.edu/tag/07CE), proof
-/

@[expose] public section

universe u v
open scoped TensorProduct

namespace Algebra.Presentation

/-- The localized conormal module complements the differentials to the free module on
its polynomial variables: if `A_a` is smooth over `R`, then
`(A_a ⊗[A] P.Cotangent) × Ω[A_a/R]` is linearly equivalent to `Fin n → A_a`. -/
theorem localized_conormal_equiv
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {n m : ℕ} (P : Algebra.Presentation R A (Fin n) (Fin m))
    (a : A) [Algebra.Smooth R (Localization.Away a)] :
    Nonempty (((Localization.Away a ⊗[A] P.toExtension.Cotangent) ×
      KaehlerDifferential R (Localization.Away a)) ≃ₗ[Localization.Away a]
      (Fin n → Localization.Away a)) := by
  classical
  let S := Localization.Away a
  let G := P.toGenerators
  let Q := (Generators.localizationAway S a).comp G
  have hf : algebraMap G.Ring A (G.σ a) = a := G.toExtension.algebraMap_σ a
  obtain ⟨_, _, r, _, e1, e2, e0, _, _, _, _, hi, ⟨ec⟩⟩ :=
    G.principal_localization_naive_cotangent a (G.σ a) hf (Bg := S)
  have : FormallySmooth R Q.toExtension.Ring := by
    change FormallySmooth R (MvPolynomial _ R)
    infer_instance
  have hQ : Function.Injective Q.toExtension.cotangentComplex :=
    Q.toExtension.cotangentComplex_injective_iff.mpr inferInstance
  let d := G.toExtension.cotangentComplex.baseChange S
  have hd : Function.Injective d := hi.mpr hQ
  let W := S ⊗[A] G.toExtension.CotangentSpace
  let D := W ⧸ LinearMap.range d
  let eqΩ : (Q.toExtension.CotangentSpace ⧸
      LinearMap.range Q.toExtension.cotangentComplex) ≃ₗ[S] KaehlerDifferential R S :=
    (Submodule.quotEquivOfEq _ _
      Q.toExtension.exact_cotangentComplex_toKaehler.linearMap_ker_eq.symm).trans
      (Q.toExtension.toKaehler.quotKerEquivOfSurjective Q.toExtension.toKaehler_surjective)
  let eD : D ≃ₗ[S] KaehlerDifferential R S := ec.trans eqΩ
  have : Module.Projective S D := Module.Projective.of_equiv eD.symm
  obtain ⟨s, hs⟩ := (LinearMap.range d).mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _))
  let e := ((LinearMap.exact_map_mkQ_range d).splitSurjectiveEquiv hd ⟨s, hs⟩).1
  let eW : W ≃ₗ[S] (Fin n → S) :=
    (G.cotangentSpaceBasis.baseChange S).equivFun
  exact ⟨((LinearEquiv.refl S _).prodCongr eD.symm).trans (e.symm.trans eW)⟩

end Algebra.Presentation
