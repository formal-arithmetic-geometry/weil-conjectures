/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.FiniteSiteInternalHomComparisonLocal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.FiniteSiteInternalHomComparisonNaturalityK
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.FiniteSiteInternalHomComparisonNaturalityM
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.FiniteSiteInternalHomComparisonEvaluation

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

/-!
# Finite-site internal-Hom comparison

Source: Bhatt--Scholze, The pro-étale topology for schemes, Lemma 6.3.16, p. 47
(blueprint: lem-sfb-finite-site-internal-hom-comparison).

The comparison map is the existing canonical evaluation transpose
`AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom`
(blueprint: def-sf-evaluation-hom-site-comparison), with its canonical tensor comparison
`AlgebraicGeometry.ProEtale.siteComparisonTensorIso`.
-/

namespace AlgebraicGeometry.ProEtale.DerivedCategory

open Scheme

set_option maxRecDepth 4096 in
/-- Blueprint `lem-sfb-finite-site-internal-hom-comparison`: finite-coefficient site comparison
preserves constructible finite-Tor internal Hom.
Source: Bhatt--Scholze, The pro-étale topology for schemes, Lemma 6.3.16, p. 47
(blueprint: lem-sfb-finite-site-internal-hom-comparison).

Let `A` be a finite commutative ring, `T` a Noetherian scheme, `K` bounded constructible of
finite Tor amplitude and `M` bounded below. The canonical evaluation transpose
`γ_{K,M} : ν^* RHom(K, M) ⟶ RHom(ν^* K, ν^* M)` is an isomorphism, natural contravariantly
in `K` and covariantly in `M`, and `ev ∘ (1 ⊗ γ) = ν^*(ev)` under the canonical tensor
comparison.

Proof (node steps):
1. A finite ring is Noetherian and `T` is qcqs, so `ν^* K` is bounded constructible of finite
   Tor amplitude (sk-cor-pe-finite-tor-comparison); `ν^*` is exact
   (lem-sf-comparison-pullback-exact), so `ν^* M ∈ D⁺`. With `H = RHom(K, M)` and the
   evaluation `e`, `γ` is the closed-structure transpose of `ν^*(e) ∘ τ⁻¹` for the canonical
   tensor comparison `τ` (lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
   lem-sf-ringed-derived-closed-symmetric-monoidal); this gives the evaluation identity, and
   naturality of `e`, `τ` and the transpose bijection give both naturality clauses.
2. For `K ∈ D^{≤ b}`, `M ∈ D^{≥ N}` both sides lie in `D^{≥ N - b}`
   (lem-weil-pbc-etale-internal-hom-lower-bound,
   lem-weil-pbc-proetale-internal-hom-lower-bound). Being an isomorphism is local; on an affine
   open `X` of a finite affine cover, by lem-weil-pbc-basis-derived-detection it suffices that
   `RΓ(W, γ)` is an isomorphism for `W = Spec B`, `B` ind-étale over `𝒪(X)`, written
   `W = lim W_i` with affine étale finitely presented stages (def-weil-pbc-ind-etale-algebra).
3. Source side: affine continuity (sk-cor-pe-affine-continuity), étale restriction
   (lem-weil-pbc-etale-inverse-image-restriction), slice restriction of internal Hom
   (lem-weil-pbc-ringed-internal-hom-exact-restriction) and the sections model
   (lem-sfb-derived-internal-hom-sections-model) give
   `RΓ(W, ν^* H) ≅ colim_i RHom_{W_i}(K_i, M_i)`.
4. Target side: weakly étale localization (lem-weil-proetale-weakly-etale-localization),
   object restriction (lem-sfb-proetale-object-inverse-image-restriction) and the pullback
   coherence (lem-pe-inverse-image-comparison-coherence) give
   `RΓ(W, RHom(ν^* K, ν^* M)) ≅ RHom_{W_proét}(ν_W^* K_W, ν_W^* M_W)`, and full faithfulness of
   `ν_W^*` on `D⁺` (sk-prop-sf-comparison) identifies it with `RHom_{W_ét}(K_W, M_W)`.
5. Constructible mapping continuity (lem-per-ind-etale-constructible-mapping-continuity) gives
   `colim_i RHom_{W_i}(K_i, M_i) ≅ RHom_{W_ét}(K_W, M_W)`; by the transpose description of
   step 1 and the coherence of step 4, `H^q RΓ(W, γ)` is the composite of these bijections.
   So `γ|_X` is an isomorphism for each `X` by basis detection, hence `γ` is one. -/
theorem isIso_finiteSiteInternalHomComparison
    (A : Type (u + 1)) [CommRing A] [Finite A] {T : Scheme.{u}} [IsNoetherian T]
    (K M : _root_.DerivedCategory
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : Etale.DerivedCategory.isBoundedConstructible A T K)
    (hKtor : ∃ a b : ℤ, Etale.DerivedCategory.hasTorAmplitudeIn A T a b K)
    (hM : ∃ N : ℤ, M.IsGE N) :
    IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) T K M) ∧
      (∀ {K' : _root_.DerivedCategory
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))} (q : K' ⟶ K),
        D(ν^*(T)[ModuleCat.{u + 1} A]).map
            (((Etale.derivedHom (ModuleCat.{u + 1} A) T).map q.op).app M) ≫
            siteComparisonEvaluationHom (ModuleCat.{u + 1} A) T K' M =
          siteComparisonEvaluationHom (ModuleCat.{u + 1} A) T K M ≫
            ((ProEtale.derivedHom (ModuleCat.{u + 1} A) T).map
              ((D(ν^*(T)[ModuleCat.{u + 1} A]).map q).op)).app
              (D(ν^*(T)[ModuleCat.{u + 1} A]).obj M)) ∧
      (∀ {M M' : _root_.DerivedCategory
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))} (q : M ⟶ M'),
        D(ν^*(T)[ModuleCat.{u + 1} A]).map
            (((Etale.derivedHom (ModuleCat.{u + 1} A) T).obj (op K)).map q) ≫
            siteComparisonEvaluationHom (ModuleCat.{u + 1} A) T K M' =
          siteComparisonEvaluationHom (ModuleCat.{u + 1} A) T K M ≫
            ((ProEtale.derivedHom (ModuleCat.{u + 1} A) T).obj
              (op (D(ν^*(T)[ModuleCat.{u + 1} A]).obj K))).map
              (D(ν^*(T)[ModuleCat.{u + 1} A]).map q)) ∧
      ((D(ν^*(T)[ModuleCat.{u + 1} A]).obj K) ◁
          siteComparisonEvaluationHom (ModuleCat.{u + 1} A) T K M) ≫
          (ProEtale.derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
            (D(ν^*(T)[ModuleCat.{u + 1} A]).obj K)).counit.app
            (D(ν^*(T)[ModuleCat.{u + 1} A]).obj M) =
        (siteComparisonTensorIso (ModuleCat.{u + 1} A) T K).inv.app
            (((Etale.derivedHom (ModuleCat.{u + 1} A) T).obj (op K)).obj M) ≫
          D(ν^*(T)[ModuleCat.{u + 1} A]).map
            ((Etale.derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K).counit.app M) := by
  have hAffine : ∀ (X : T.Opens), IsAffine X →
      IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X
        ((Etale.upperStar (ModuleCat.{u + 1} A) X.ι).mapDerivedCategory.obj K)
        ((Etale.upperStar (ModuleCat.{u + 1} A) X.ι).mapDerivedCategory.obj M)) := by
    intro X hX
    exact isIso_finiteSiteInternalHomComparison_affine A K M hK hKtor hM hX
  have hIso := isIso_finiteSiteInternalHomComparison_of_affine_opens A K M hK hKtor hM hAffine
  exact ⟨hIso,
    finiteSiteInternalHomComparison_naturality_K A K M,
    finiteSiteInternalHomComparison_naturality_M A K M,
    finiteSiteInternalHomComparison_evaluation A K M⟩

end AlgebraicGeometry.ProEtale.DerivedCategory
