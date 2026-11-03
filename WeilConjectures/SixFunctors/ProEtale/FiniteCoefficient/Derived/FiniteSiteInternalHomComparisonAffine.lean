/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.DerivedCategory

open Scheme

/-- Legacy affine finite-site internal-Hom comparison retained for compatibility while its
archived DAG node is removed from the current blueprint route. On an affine open `X` of the
Noetherian scheme `T`, the evaluation-transpose comparison of the restrictions `K|_X`, `M|_X`
is an isomorphism.

Source: Bhatt--Scholze, The pro-étale topology for schemes, Lemma 6.3.16, p. 47
(legacy blueprint: new-sfb-finite-site-internal-hom-affine; archived after route review;
steps 2-5 of
lem-sfb-finite-site-internal-hom-comparison on the affine open `X`).

Proof in words. `X` is affine Noetherian, `K|_X` is bounded constructible of finite Tor
amplitude and `M|_X ∈ D^+`. By the étale and pro-étale internal-Hom lower bounds both sides
are bounded below, so by the basis detection lemma it suffices that `RΓ(W, γ)` is an
isomorphism for every `W = Spec B`, `B` ind-étale over `O(X)`; write `W = lim W_i` with
`W_i → X` affine étale. Source side: affine continuity, étale restriction and the sections
model give `RΓ(W, ν^* H) ≅ colim_i RHom(K_i, M_i)`. Target side: the weakly-étale
localization, pro-étale-object restriction and the pullback-comparison coherence give
`RΓ(W, H_p) ≅ RHom(ν_W^* K_W, ν_W^* M_W)`, and full faithfulness of `ν_W^*` on `D^+`
identifies it with `RHom(K_W, M_W)`. Constructible mapping continuity makes
`colim_i RHom(K_i, M_i) → RHom(K_W, M_W)` an isomorphism, and the evaluation description of
`γ` identifies `H^q RΓ(W, γ)` with the composite of these bijections. -/
theorem isIso_finiteSiteInternalHomComparison_affine
    (A : Type (u + 1)) [CommRing A] [Finite A] {T : Scheme.{u}} [IsNoetherian T]
    (K M : _root_.DerivedCategory
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : Etale.DerivedCategory.isBoundedConstructible A T K)
    (hKtor : ∃ a b : ℤ, Etale.DerivedCategory.hasTorAmplitudeIn A T a b K)
    (hM : ∃ N : ℤ, M.IsGE N)
    {X : T.Opens} (hX : IsAffine X) :
    IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X
      ((Etale.upperStar (ModuleCat.{u + 1} A) X.ι).mapDerivedCategory.obj K)
      ((Etale.upperStar (ModuleCat.{u + 1} A) X.ι).mapDerivedCategory.obj M)) := by
  sorry

end AlgebraicGeometry.ProEtale.DerivedCategory
