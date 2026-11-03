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

/-- Naturality of the evaluation transpose for a general coefficient category. Stated with
abstract instances, so that the kernel checks the unfolding of `siteComparisonEvaluationHom`
once and not at the concrete `ModuleCat` instances. -/
private theorem siteComparisonEvaluationHom_naturality
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) [(comparisonUpperStar B X).PreservesFlat]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B))
    {M M' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)} (q : M ⟶ M') :
    (comparisonUpperStar B X).mapDerivedCategory.map
        (((Etale.derivedHom B X).obj (op K)).map q) ≫
        siteComparisonEvaluationHom B X K M' =
      siteComparisonEvaluationHom B X K M ≫
        ((ProEtale.derivedHom B X).obj
          (op ((comparisonUpperStar B X).mapDerivedCategory.obj K))).map
          ((comparisonUpperStar B X).mapDerivedCategory.map q) := by
  let F := (comparisonUpperStar B X).mapDerivedCategory
  let _ : F.Monoidal := siteComparisonDerivedMonoidal B X
  unfold siteComparisonEvaluationHom
  exact (Functor.LaxMonoidal.ihomComparison F K).natTrans.naturality q

/-- Naturality in the covariant internal-Hom argument for the finite-site comparison.
Source: the transpose naturality part of Bhatt--Scholze, Lemma 6.3.16
(blueprint: new-sfb-finite-site-internal-hom-naturality-m; step 1 of
lem-sfb-finite-site-internal-hom-comparison).

Proof in words. `siteComparisonEvaluationHom T K -` is the family of components of the natural
transformation `(ihomComparison F K).natTrans` of `F = ν_T^*` with the chosen monoidal
structure `siteComparisonDerivedMonoidal`; the identity is its naturality square at `q`. -/
theorem finiteSiteInternalHomComparison_naturality_M
    (A : Type (u + 1)) [CommRing A] [Finite A] {T : Scheme.{u}} [IsNoetherian T]
    (K M : _root_.DerivedCategory
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ∀ {M M' : _root_.DerivedCategory
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))} (q : M ⟶ M'),
      D(ν^*(T)[ModuleCat.{u + 1} A]).map
          (((Etale.derivedHom (ModuleCat.{u + 1} A) T).obj (op K)).map q) ≫
          siteComparisonEvaluationHom (ModuleCat.{u + 1} A) T K M' =
        siteComparisonEvaluationHom (ModuleCat.{u + 1} A) T K M ≫
          ((ProEtale.derivedHom (ModuleCat.{u + 1} A) T).obj
            (op (D(ν^*(T)[ModuleCat.{u + 1} A]).obj K))).map
            (D(ν^*(T)[ModuleCat.{u + 1} A]).map q) := by
  intro M M' q
  exact siteComparisonEvaluationHom_naturality (ModuleCat.{u + 1} A) T K q

end AlgebraicGeometry.ProEtale.DerivedCategory
