/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NW
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

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

-- The abstract counit factorization, transported from the homotopy localization to Q.
private theorem chainCounit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {L : C ⥤ D} {G : D ⥤ C} [L.Additive] [G.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (a : L ⊣ G)
    (K : CochainComplex D ℤ) :
    L.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ K) ≫
        a.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj K) =
      L.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app K) := by
  have h := (a.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso D (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    G.rightDerivedFunctorUnit ((HomotopyCategory.quotient D _).obj K)
  change L.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient D _).obj K)) ≫
    a.mapDerivedCategoryRightDerivedAdjunction.counit.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient D _).obj K)) = _ at h
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient] at h
  erw [L.mapDerivedCategoryFactorsh_hom_app] at h
  have hq (Y : CochainComplex C ℤ) :
      (DerivedCategory.quotientCompQhIso C).hom.app Y = 𝟙 _ := rfl
  have hqi (Y : CochainComplex D ℤ) :
      (DerivedCategory.quotientCompQhIso D).inv.app Y = 𝟙 _ := rfl
  simp only [hq, hqi, Functor.mapHomotopyCategoryFactors,
    Quotient.lift.isLift_inv, Functor.comp_obj] at h
  erw [CategoryTheory.Functor.map_id, DerivedCategory.Qh.map_id] at h
  simp only [Category.id_comp, Category.comp_id] at h
  have hunit : G.rightDerivedFunctorUnitQ K = G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient D _).obj K) := by
    simp only [Functor.rightDerivedFunctorUnitQ,
      show (DerivedCategory.quotientCompQhIso C).inv.app
        ((G.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ from rfl,
      show (DerivedCategory.quotientCompQhIso D).hom.app K = 𝟙 _ from rfl,
      Category.id_comp]
    erw [G.rightDerivedFunctor.map_id, Category.comp_id]
  rw [hunit]
  exact h

-- Naturality and chain transposes follow from any adjunction with this counit square.
private theorem chainTranspose
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {L : C ⥤ D} {G : D ⥤ C} [L.Additive] [G.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (a : L ⊣ G)
    (d : L.mapDerivedCategory ⊣ G.rightDerivedFunctor)
    (hc : ∀ K : CochainComplex D ℤ,
      L.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ K) ≫
          d.counit.app (DerivedCategory.Q.obj K) =
        L.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app K)) :
    (∀ (M : CochainComplex C ℤ)
      (K : CochainComplex D ℤ)
      (f : M ⟶ (G.mapHomologicalComplex (.up ℤ)).obj K),
      (d.homEquiv
        (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj K)).symm
          (DerivedCategory.Q.map f ≫
            G.rightDerivedFunctorUnitQ K) =
        L.mapDerivedCategoryFactors.hom.app M ≫
          DerivedCategory.Q.map
            ((L.mapHomologicalComplex (.up ℤ)).map f ≫
              (a.mapHomologicalComplex
                (.up ℤ)).counit.app K)) ∧
    (∀ (K K' : CochainComplex D ℤ)
      (k : K ⟶ K'),
      DerivedCategory.Q.map
          ((G.mapHomologicalComplex (.up ℤ)).map k) ≫
            G.rightDerivedFunctorUnitQ K' =
        G.rightDerivedFunctorUnitQ K ≫
          G.rightDerivedFunctor.map
            (DerivedCategory.Q.map k)) ∧
    (∀ (M M' : CochainComplex C ℤ)
      (K K' : CochainComplex D ℤ)
      (b : M' ⟶ M) (k : K ⟶ K')
      (f : M ⟶ (G.mapHomologicalComplex (.up ℤ)).obj K),
      (d.homEquiv
        (DerivedCategory.Q.obj M') (DerivedCategory.Q.obj K')).symm
          (DerivedCategory.Q.map (b ≫ f ≫
            (G.mapHomologicalComplex (.up ℤ)).map k) ≫
              G.rightDerivedFunctorUnitQ K') =
        L.mapDerivedCategory.map
          (DerivedCategory.Q.map b) ≫
          (d.homEquiv
            (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj K)).symm
              (DerivedCategory.Q.map f ≫
                G.rightDerivedFunctorUnitQ K) ≫
          DerivedCategory.Q.map k) ∧
    (∀ K : CochainComplex D ℤ,
      L.mapDerivedCategory.map
          (G.rightDerivedFunctorUnitQ K) ≫
          d.counit.app
            (DerivedCategory.Q.obj K) =
        L.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((a.mapHomologicalComplex
              (.up ℤ)).counit.app K)) := by
  refine ⟨?_, ?_, ?_, hc⟩
  · intro M K f
    rw [d.homEquiv_counit, Functor.map_comp, Category.assoc, hc]
    rw [← Category.assoc, L.mapDerivedCategoryFactors_hom_naturality]
    rw [Category.assoc, ← DerivedCategory.Q.map_comp]
  · intro K K' k
    exact G.rightDerivedFunctorUnitQ_naturality k
  · intro M M' K K' b k f
    simp only [Functor.map_comp, Category.assoc]
    rw [G.rightDerivedFunctorUnitQ_naturality]
    rw [← Category.assoc (DerivedCategory.Q.map f),
      d.homEquiv_naturality_left_symm, d.homEquiv_naturality_right_symm]

/-- The canonical unbounded étale derived adjunction sends an ordinary chain transpose
through localization, naturally in both complexes, and its counit has the ordinary
counit normalization.

Source: Stacks Project, sites-cohomology.tex, Tags 07A6 and 0FPI; derived.tex,
Tags 0FND and 0DVC (blueprint: lem-sp-etale-derived-chain-transpose).

The existing `mapDerivedUpperStarLowerStarAdjunction` supplies the adjunction, with
`upperStar.mapDerivedCategory` as its left adjoint. `rightDerivedFunctorUnitQ` is the
canonical K-injective comparison on complexes. `mapDerivedCategoryFactors` is the
exact termwise identification, written explicitly in the first and fourth clauses.

Proof: apply the canonical derived counit factorization
`Adjunction.derivedε_fac_app` to the homotopy adjunction. Transport it to complexes
using `mapHomotopyCategory_counit_app_quotient` and the exact-pullback comparison.
The quotient comparison has identity components, so this is the fourth clause.
For the first clause, the inverse Hom equivalence is left-adjoint action followed
by the counit; use the fourth clause and naturality of the exact-pullback comparison.
The second clause is comparison naturality. For the third, use comparison naturality
and the two naturality laws of the inverse Hom equivalence. All complexes are
unbounded, and the right adjoint need not preserve quasi-isomorphisms. -/
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
  have hd : mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) r =
      Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) r) := rfl
  rw [hd]
  exact chainTranspose (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) r)
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) r))
    (chainCounit (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) r))

end AlgebraicGeometry.Etale
