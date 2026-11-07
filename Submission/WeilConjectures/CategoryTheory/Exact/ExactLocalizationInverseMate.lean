/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Submission.WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Localization.Adjunction

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Exact localization and inverse mates

Source: Stacks Project, Tag 07A7 (remark-base-change), and the inverse-mate
compatibility sentence of `fix-prop-coherence`.
(blueprint: lem-sf-exact-localization-inverse-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The exact adjunction obtained by localizing a specified termwise adjunction,
with independent universes on its two abelian categories. This item helper uses
the same construction as `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`;
when the universes agree, the two definitions are definitionally equal. Source: Stacks Tag 015F
(blueprint: lem-sf-exact-localization-inverse-mate). -/
def exactLocalizationDerivedAdjunction
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    F.mapDerivedCategory ⊣ G.mapDerivedCategory := by
  letI : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory :=
    ⟨(Functor.mapDerivedCategoryFactors F).symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory :=
    ⟨(Functor.mapDerivedCategoryFactors G).symm⟩
  exact (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory

/-- The localized unit, using the specified exact-functor factorizations. -/
private lemma exact_unit_app
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R)
    (K : CochainComplex C ℤ) :
    (exactLocalizationDerivedAdjunction a).unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        R.mapDerivedCategoryFactors.inv.app _ ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app K) := by
  unfold exactLocalizationDerivedAdjunction
  rw [Adjunction.localization_unit_app]
  rfl

/-- The localized Hom bijection agrees with the cochain Hom bijection. -/
private lemma exact_hom_fac
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R)
    (K : CochainComplex C ℤ) (N : CochainComplex D ℤ)
    (f : (L.mapHomologicalComplex (.up ℤ)).obj K ⟶ N) :
    (exactLocalizationDerivedAdjunction a).homEquiv
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj N)
        (L.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
        R.mapDerivedCategoryFactors.inv.app N := by
  rw [Adjunction.homEquiv_unit, exact_unit_app, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Functor.map_id, Category.id_comp]
  exact congrArg
    (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫ ·)
    (R.mapDerivedCategoryFactors.inv.naturality f).symm


end CategoryTheory
