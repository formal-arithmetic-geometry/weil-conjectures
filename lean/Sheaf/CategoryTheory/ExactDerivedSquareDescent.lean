/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Descent of an evaluation square of exact functors

A commuting square of chain transformations remains a commuting square after
ordinary unbounded derived localization and its canonical factorization comparisons.
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

private theorem derivedEvaluation_fac
    {A B C T : Type*} [Category A] [Category B] [Category C] [Category T]
    [Abelian A] [Abelian B] [Abelian C] [Abelian T]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory T]
    (U : A ⥤ B) (V : B ⥤ T) (F : A ⥤ C) (R : C ⥤ T)
    [U.Additive] [V.Additive] [F.Additive] [R.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : U ⋙ V ≅ F ⋙ R) (X : CochainComplex A ℤ) :
    ((Functor.mapDerivedCategoryCompIso U V).symm ≪≫
        Functor.mapDerivedCategoryNatIso a ≪≫
        Functor.mapDerivedCategoryCompIso F R).hom.app (DerivedCategory.Q.obj X) ≫
      R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
      R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj X) =
    V.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app X) ≫
      V.mapDerivedCategoryFactors.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj X) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app X) := by
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  erw [Category.assoc, Category.assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factors]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso U V).hom.app
    (DerivedCategory.Q.obj X))).1
  erw [Iso.hom_inv_id_app_assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  exact Functor.mapDerivedCategoryNatIso_fac a X

/-- Conjugating a descended transformation by a derived evaluation square gives
its evaluated descent.
Source: Stacks Tags 015F and 04VG, exact-functor factorization and localization
(blueprint: lem-trf-exact-derived-square-descent).
Proof: localization extensionality reduces equality of the two natural
transformations to complexes. Cancel the source square isomorphism and the two
target factorization isomorphisms. Naturality moves the evaluated descent past
the source factorization. The prescribed descent equations and the composition
and natural-isomorphism factorization identities then identify both sides with
Q applied to the chain-level commuting square. Evaluating this equality of
natural transformations at X gives the result. No boundedness hypothesis enters.
The identity and zero functor cases satisfy the same argument. -/
theorem evaluated_descent
    {A B C T : Type*} [Category A] [Category B] [Category C] [Category T]
    [Abelian A] [Abelian B] [Abelian C] [Abelian T]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory T]
    (U U' : A ⥤ B) (V : B ⥤ T) (F : A ⥤ C) (R S : C ⥤ T)
    [U.Additive] [U'.Additive] [V.Additive] [F.Additive] [R.Additive] [S.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (a : U ⋙ V ≅ F ⋙ R) (b : U' ⋙ V ≅ F ⋙ S)
    (τ : U.mapHomologicalComplex (.up ℤ) ⟶ U'.mapHomologicalComplex (.up ℤ))
    (σ : R.mapHomologicalComplex (.up ℤ) ⟶ S.mapHomologicalComplex (.up ℤ))
    (I : U.mapDerivedCategory ⟶ U'.mapDerivedCategory)
    (J : R.mapDerivedCategory ⟶ S.mapDerivedCategory)
    (hI : ∀ X, I.app (DerivedCategory.Q.obj X) ≫
      U'.mapDerivedCategoryFactors.hom.app X =
        U.mapDerivedCategoryFactors.hom.app X ≫ DerivedCategory.Q.map (τ.app X))
    (hJ : ∀ X, J.app (DerivedCategory.Q.obj X) ≫
      S.mapDerivedCategoryFactors.hom.app X =
        R.mapDerivedCategoryFactors.hom.app X ≫ DerivedCategory.Q.map (σ.app X))
    (h : ∀ X, (V.mapHomologicalComplex (.up ℤ)).map (τ.app X) ≫
      (NatTrans.mapHomologicalComplex b.hom (.up ℤ)).app X =
        (NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app X ≫
          σ.app ((F.mapHomologicalComplex (.up ℤ)).obj X))
    (X : DerivedCategory A) :
    ((Functor.mapDerivedCategoryCompIso U V).symm ≪≫
        Functor.mapDerivedCategoryNatIso a ≪≫
        Functor.mapDerivedCategoryCompIso F R).inv.app X ≫
      V.mapDerivedCategory.map (I.app X) ≫
      ((Functor.mapDerivedCategoryCompIso U' V).symm ≪≫
        Functor.mapDerivedCategoryNatIso b ≪≫
        Functor.mapDerivedCategoryCompIso F S).hom.app X =
      J.app (F.mapDerivedCategory.obj X) := by
  let aD := (Functor.mapDerivedCategoryCompIso U V).symm ≪≫
    Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryCompIso F R
  let bD := (Functor.mapDerivedCategoryCompIso U' V).symm ≪≫
    Functor.mapDerivedCategoryNatIso b ≪≫ Functor.mapDerivedCategoryCompIso F S
  have hh : aD.inv ≫ Functor.whiskerRight I V.mapDerivedCategory ≫ bD.hom =
      Functor.whiskerLeft F.mapDerivedCategory J := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
    intro M
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    apply (cancel_epi (aD.hom.app (DerivedCategory.Q.obj M))).1
    apply (cancel_mono (S.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app M) ≫
      S.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M))).1
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← J.naturality_assoc]
    dsimp only [Functor.comp_obj]
    rw [hJ, reassoc_of% (derivedEvaluation_fac U V F R a M),
      derivedEvaluation_fac U' V F S b M]
    rw [← V.mapDerivedCategory.map_comp_assoc, hI]
    simp only [Functor.map_comp, Category.assoc]
    erw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
    rw [← DerivedCategory.Q.map_comp, h]
    simp only [Functor.map_comp]
  exact congrArg (fun f ↦ f.app X) hh

end CategoryTheory.Functor
