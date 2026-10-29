/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralLisseLocalStructure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible

/-!
# Integral local models

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, uniformizer `ϖ` and
residue field `𝔽_E`, and `X` a noetherian scheme. Blueprint `sk-prop-integral-local-structure`
(section `sec-proetale-coefficients`; Bhatt–Scholze, *The pro-étale topology for schemes*,
Lemma 6.8.10 and the proof of Proposition 6.8.11): if `K ∈ D(X_proét, 𝒪_E)` is derived complete
and its first derived reduction `K₁ = K ⊗ᴸ 𝔽_E` is bounded constructible, there is a finite
stratification of `X` such that on each stratum `S`, pro-étale locally,
`K|_S ≃ 𝒪_{E,S} ⊗_{𝒪_E} P^•` for a bounded complex `P^•` of finite free `𝒪_E`-modules, with
cohomology in a fixed range.

Over the discrete valuation ring `𝒪_E` such a complex `P^•` is quasi-isomorphic to the sum of its
shifted cohomology modules, which are finitely generated, i.e. of the form `⊕ⱼ 𝒪_E/ϖ^{eⱼ} ⊕ 𝒪_E^r`.
The statement `ProEtale.exists_stratification_cover_homology_iso_integralConstantModule` records
the cohomology sheaves of the local models: on the members of a pro-étale cover of each stratum,
the cohomology sheaves of the pullback of `K` are the constant modules
`ProEtale.integralConstantModule`, and vanish outside a fixed interval.

## Sorried input

`ProEtale.exists_stratification_cover_homology_iso_integralConstantModule` is `sorry`ed: it is
blueprint `sk-prop-integral-local-structure`, whose proof (local models at the finite levels
`K ⊗ᴸ 𝒪_E/ϖⁿ`, blueprints `sk-lem-integral-finite-levels` and `sk-lem-integral-scalar-towers`, made
compatible by a Mittag–Leffler argument on a weakly contractible cover) is not formalized.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

/-- Blueprint `sk-prop-integral-local-structure` (section `sec-proetale-coefficients`;
Bhatt–Scholze, Lemma 6.8.10): on a noetherian scheme `X`, let `K` be a derived complete complex of
`𝒪_{E,X}`-module objects whose first derived reduction lies in `Dᵇc(X, 𝔽_E)`. Then there are an
interval `[a, b]` and a finite stratification of `X` such that every stratum has a pro-étale cover
on whose members `g : W ⟶ X` the pullback `Lg^* K` is a local model `𝒪_{E,W} ⊗_{𝒪_E} P^•`: its
cohomology sheaves are constant finitely generated modules `⊕ⱼ 𝒪_E/ϖ^{eⱼ} ⊕ 𝒪_E^r`, zero outside
`[a, b]`. -/
theorem exists_stratification_cover_homology_iso_integralConstantModule {X : Scheme.{u}}
    [IsNoetherian X]
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK : derivedCompleteIntegers ℓ E X K)
    (h₁ : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) X ((derivedReduction X ℓ E).obj K))
    (ϖ : PadicAlgCl.integers ℓ E.1)
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {ϖ}) :
    ∃ (a b : ℤ) (S : Scheme.Stratification X), ∀ s : Fin S.n,
      ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain s), ∀ (i : 𝒰.I₀) (q : ℤ),
        ((q < a ∨ b < q) → IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((L((𝒰.f i ≫ S.immersion s)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K))) ∧
        ∃ (k r : ℕ) (e : Fin k → ℕ), Nonempty ((DerivedCategory.homologyFunctor _ q).obj
          ((L((𝒰.f i ≫ S.immersion s)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K) ≅
            integralConstantModule ℓ E.1 (𝒰.X i) ϖ k r e) :=
  sorry

end AlgebraicGeometry.ProEtale
