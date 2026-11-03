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

private theorem siteComparisonEvaluationHom_naturality_left
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (T : Scheme.{u}) [(comparisonUpperStar B T).PreservesFlat]
    {K K' : _root_.DerivedCategory (Sheaf T.smallEtaleTopology B)}
    (q : K' ⟶ K) (M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology B)) :
    (comparisonUpperStar B T).mapDerivedCategory.map
        (((Etale.derivedHom B T).map q.op).app M) ≫
        siteComparisonEvaluationHom B T K' M =
      siteComparisonEvaluationHom B T K M ≫
        ((ProEtale.derivedHom B T).map
          ((comparisonUpperStar B T).mapDerivedCategory.map q).op).app
            ((comparisonUpperStar B T).mapDerivedCategory.obj M) := by
  let F := (comparisonUpperStar B T).mapDerivedCategory
  let _ : F.Monoidal := siteComparisonDerivedMonoidal B T
  unfold siteComparisonEvaluationHom
  exact Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app F q M

/-- Naturality in the contravariant internal-Hom argument for the finite-site comparison.
Source: the transpose naturality part of Bhatt--Scholze, Lemma 6.3.16
(blueprint: new-sfb-finite-site-internal-hom-naturality-k; step 1 of
lem-sfb-finite-site-internal-hom-comparison).

Proof in words. `siteComparisonEvaluationHom` is the component of the lax-monoidal
internal-Hom comparison `ihomComparison F K` of `F = ν_T^*` with the chosen monoidal structure
`siteComparisonDerivedMonoidal`; the identity is the instance
`Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app F q M` (naturality of the comparison in
the first variable, from naturality of evaluation and of the tensorator), `derivedHom` being
`MonoidalClosed.internalHom`, whose action on `q.op` is `pre q`. -/
theorem finiteSiteInternalHomComparison_naturality_K
    (A : Type (u + 1)) [CommRing A] [Finite A] {T : Scheme.{u}} [IsNoetherian T]
    (K M : _root_.DerivedCategory
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ∀ {K' : _root_.DerivedCategory
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))} (q : K' ⟶ K),
      D(ν^*(T)[ModuleCat.{u + 1} A]).map
          (((Etale.derivedHom (ModuleCat.{u + 1} A) T).map q.op).app M) ≫
          siteComparisonEvaluationHom (ModuleCat.{u + 1} A) T K' M =
        siteComparisonEvaluationHom (ModuleCat.{u + 1} A) T K M ≫
          ((ProEtale.derivedHom (ModuleCat.{u + 1} A) T).map
            ((D(ν^*(T)[ModuleCat.{u + 1} A]).map q).op)).app
            (D(ν^*(T)[ModuleCat.{u + 1} A]).obj M) := by
  intro K' q
  exact siteComparisonEvaluationHom_naturality_left (ModuleCat.{u + 1} A) T q M

end AlgebraicGeometry.ProEtale.DerivedCategory
