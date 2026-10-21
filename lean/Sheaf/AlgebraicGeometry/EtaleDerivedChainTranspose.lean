/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NW
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.CategoryTheory.KInjectiveTotalDerived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # The canonical étale derived adjunction on chain transposes

Source: Stacks Project, sites-cohomology.tex, Tags 07A6 and 0FPI
(lemma-adjoint and lemma-adjoints-push-pull-compatibility), and derived.tex,
Tags 0FND and 0DVC (blueprint: lem-sp-etale-derived-chain-transpose).

We use the existing unbounded derived adjunction, its exact termwise pullback,
and the existing cochain comparison `Functor.rightDerivedFunctorUnitQ`.
The four clauses are the chain-transpose formula, comparison naturality,
bifunctoriality of the transpose formula, and its counit specialization.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical unbounded étale derived adjunction sends an ordinary chain transpose
through localization, naturally in both complexes, and its counit has the ordinary
counit normalization.

Source: Stacks Project, sites-cohomology.tex, Tags 07A6 and 0FPI; derived.tex,
Tags 0FND and 0DVC (blueprint: lem-sp-etale-derived-chain-transpose).

The existing `mapDerivedUpperStarLowerStarAdjunction` supplies the adjunction, with
`upperStar.mapDerivedCategory` as its left adjoint. `rightDerivedFunctorUnitQ` is the
canonical K-injective comparison on complexes. `mapDerivedCategoryFactors` is the
exact termwise identification, written explicitly in the first and fourth clauses.

Proof plan:
1. The exact constant-coefficient inverse image and its right adjoint give the
termwise and homotopy adjunctions (prop-weil-pbc-inverse-image-modules-exact,
lem-weil-pbc-termwise-adjunction-homotopy). Exactness descends the left adjoint
termwise by lem-weil-pbc-exact-functor-derived-factorization.
2. Small-site size conventions and K-injective resolutions give the canonical
right-derived pair and comparison (def-weil-size-convention,
prop-pur-kinjective-resolutions-exist, lem-weil-pbc-kinjective-total-derived).
The additive pushforward preserves cone matrices and shifts, so its homotopy
functor followed by localization is exact (def-weil-abstract-derived-category,
lem-pur-homotopy-category-triangulated).
3. Choose a quasi-isomorphism j : K → I to a K-injective complex. The right
adjoint preserves K-injectives (lem-weil-pbc-right-adjoint-preserves-kinjective).
The canonical computation c_j identifies the derived pushforward with Q(GI),
and comparison naturality gives c_j α_K = Q(Gj), without asserting that Gj
is a quasi-isomorphism (lem-sf-kinjective-derived-map-computation).
4. Compute Hom into GI and I in the homotopy categories using the K-injective
Hom bijections (lem-weil-pbc-kinjective-hom-derived), apply the homotopy
adjunction, then cancel Qj. This constructs the derived Hom bijection.
5. The unique homotopy-class lift between resolutions proves independence and
naturality in the target. Naturality in source chain maps follows from the
ordinary adjunction and extends through localization
(lem-sf-kinjective-derived-map-computation,
lem-weil-pbc-localization-universal-property).
6. The natural Hom bijections define the canonical adjunction
(lem-weil-pbc-adjunction-of-natural-bijection). The map Qf followed by α_K
is represented on I by Gj composed with f. Its ordinary transpose is j
composed with the transpose of f, by counit naturality. Cancelling Qj gives
the first clause.
7. Naturality of the comparison and both adjunction transposes gives the second
and third clauses. Set M = GK and f = identity in the first clause and use
the counit formula for the inverse Hom bijection to obtain the fourth clause.
All complexes and resolutions are unbounded; no flatness or geometric
hypothesis on r is used. -/
theorem etaleDerivedChainTranspose (R : Type (u + 1)) [CommRing R]
    {W V : Scheme.{u}} (r : W ⟶ V) :
    (∀ (M : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
      (K : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
      (f : M ⟶ ((lowerStar (ModuleCat.{u + 1} R) r).mapHomologicalComplex (.up ℤ)).obj K),
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) r).homEquiv
        (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj K)).symm
          (DerivedCategory.Q.map f ≫
            (lowerStar (ModuleCat.{u + 1} R) r).rightDerivedFunctorUnitQ K) =
        (upperStar (ModuleCat.{u + 1} R) r).mapDerivedCategoryFactors.hom.app M ≫
          DerivedCategory.Q.map
            (((upperStar (ModuleCat.{u + 1} R) r).mapHomologicalComplex (.up ℤ)).map f ≫
              ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) r).mapHomologicalComplex
                (.up ℤ)).counit.app K)) ∧
    (∀ (K K' : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
      (k : K ⟶ K'),
      DerivedCategory.Q.map
          (((lowerStar (ModuleCat.{u + 1} R) r).mapHomologicalComplex (.up ℤ)).map k) ≫
            (lowerStar (ModuleCat.{u + 1} R) r).rightDerivedFunctorUnitQ K' =
        (lowerStar (ModuleCat.{u + 1} R) r).rightDerivedFunctorUnitQ K ≫
          (lowerStar (ModuleCat.{u + 1} R) r).rightDerivedFunctor.map
            (DerivedCategory.Q.map k)) ∧
    (∀ (M M' : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
      (K K' : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
      (b : M' ⟶ M) (k : K ⟶ K')
      (f : M ⟶ ((lowerStar (ModuleCat.{u + 1} R) r).mapHomologicalComplex (.up ℤ)).obj K),
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) r).homEquiv
        (DerivedCategory.Q.obj M') (DerivedCategory.Q.obj K')).symm
          (DerivedCategory.Q.map (b ≫ f ≫
            ((lowerStar (ModuleCat.{u + 1} R) r).mapHomologicalComplex (.up ℤ)).map k) ≫
              (lowerStar (ModuleCat.{u + 1} R) r).rightDerivedFunctorUnitQ K') =
        (upperStar (ModuleCat.{u + 1} R) r).mapDerivedCategory.map
          (DerivedCategory.Q.map b) ≫
          ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) r).homEquiv
            (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj K)).symm
              (DerivedCategory.Q.map f ≫
                (lowerStar (ModuleCat.{u + 1} R) r).rightDerivedFunctorUnitQ K) ≫
          DerivedCategory.Q.map k) ∧
    (∀ K : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ,
      (upperStar (ModuleCat.{u + 1} R) r).mapDerivedCategory.map
          ((lowerStar (ModuleCat.{u + 1} R) r).rightDerivedFunctorUnitQ K) ≫
          (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) r).counit.app
            (DerivedCategory.Q.obj K) =
        (upperStar (ModuleCat.{u + 1} R) r).mapDerivedCategoryFactors.hom.app
          (((lowerStar (ModuleCat.{u + 1} R) r).mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) r).mapHomologicalComplex
              (.up ℤ)).counit.app K)) := by
  sorry

end AlgebraicGeometry.Etale
