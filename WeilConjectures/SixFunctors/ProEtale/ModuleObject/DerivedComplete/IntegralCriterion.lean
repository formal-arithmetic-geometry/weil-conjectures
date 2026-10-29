/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.IntegralCriterionLocal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible

/-!
# The integral constructibility criterion

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and residue field
`𝔽_E`, and `X` a noetherian scheme. Blueprint `sk-prop-integral-criterion` (section
`sec-proetale-coefficients`) characterizes the bounded constructible `𝒪_E`-complexes on
`X_proét`: a complex `K` is bounded constructible if and only if it is derived complete and its
first derived reduction `K₁ = K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` is a bounded constructible complex of
`𝔽_E`-sheaves (Bhatt–Scholze, *The pro-étale topology for schemes*, Proposition 6.8.11; Stacks,
Tag 09C7).

The implication (1) ⇒ (2) is proved:
`ProEtale.derivedCompleteIntegers_of_boundedConstructible` and
`ProEtale.boundedConstructible_derivedReduction_obj`. This file states the converse
(2) ⇒ (1), `ProEtale.boundedConstructible_of_derivedCompleteIntegers`.

## Proof of (2) ⇒ (1)

By the integral local models of blueprint `sk-prop-integral-local-structure`
(`ProEtale.exists_stratification_cover_homology_iso_integralConstantModule`), there are an
interval `[a, b]`, a finite stratification of `X` and pro-étale covers of its strata on whose
members `g` the cohomology sheaves `Hⁿ(Lg^* K) ≅ g^* Hⁿ(K)` are constant finitely presented
modules `⊕ⱼ 𝒪_E/ϖ^{eⱼ} ⊕ 𝒪_E^r`, zero outside `[a, b]`. Hence every `Hⁿ(K)` is constructible
along this stratification, and `Hⁿ(K)` vanishes outside `[a, b]`, the pullbacks to the members of
the covers jointly detecting zero objects.

## Remaining input

The local structure statement
`ProEtale.exists_stratification_cover_homology_iso_integralConstantModule` is `sorry`ed.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

/-- Blueprint `sk-prop-integral-criterion` (section `sec-proetale-coefficients`), implication
(2) ⇒ (1): on a noetherian scheme `X`, a derived complete complex `K` of `𝒪_{E,X}`-module
objects whose first derived reduction `K₁ = K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` lies in `Dᵇc(X, 𝔽_E)` is
bounded constructible (Bhatt–Scholze, Proposition 6.8.11). -/
theorem boundedConstructible_of_derivedCompleteIntegers {X : Scheme.{u}} [IsNoetherian X]
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK : derivedCompleteIntegers ℓ E X K)
    (h₁ : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) X ((derivedReduction X ℓ E).obj K)) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E.1
  rw [Ideal.submodule_span_eq] at hϖ
  obtain ⟨a, b, S, hS⟩ :=
    exists_stratification_cover_homology_iso_integralConstantModule hK h₁ ϖ hϖ
  choose 𝒰 h𝒰 using hS
  refine (mem_boundedConstructible_iff _ K).2 ⟨⟨a, b, fun q hq ↦ ?_⟩, fun n ↦ ?_⟩
  · exact isZero_of_forall_isZero_upperStar_stratification _ S 𝒰 _ fun s i ↦
      ((h𝒰 s i q).1 hq).of_iso ((leftDerivedUpperStarHomologyIso _ _ q).app K)
  · refine isConstructibleModuleObject_of_isFinitelyPresented_upperStar _ S 𝒰 _ fun s i ↦ ?_
    obtain ⟨k, r, e, ⟨φ⟩⟩ := (h𝒰 s i n).2
    exact (isFinitelyPresented_integralConstantModule ℓ E.1 _ ϖ k r e).of_iso
      (((leftDerivedUpperStarHomologyIso _ _ n).app K) ≪≫ φ).symm

end AlgebraicGeometry.ProEtale
