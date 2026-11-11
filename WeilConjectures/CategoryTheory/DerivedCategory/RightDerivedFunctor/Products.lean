/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit

/-!
# Unbounded right derived functors preserve products and derived limits

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has K-injective
resolutions and products of shape `J`, and products of shape `J` exist and are exact in `D`. If
`F` preserves products of shape `J`, then so does its unbounded right derived functor
`F.rightDerivedFunctor : D(C) ⥤ D(D)`: a product of K-injective complexes is K-injective and is a
product in `D(C)`, `R(F)` is computed on it by applying `F` termwise, and a termwise product of
complexes is a product in `D(D)` since products are exact in `D` (Stacks, Tag 08U1).

Being triangulated, `F.rightDerivedFunctor` then also preserves derived inverse limits of towers
(homotopy limits), when `F` preserves countable products.

## Main statements

- `CategoryTheory.Functor.preservesLimitsOfShape_discrete_rightDerivedFunctor`;
- `CategoryTheory.Functor.isHomotopyLimit_rightDerivedFunctor_mapCone`.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive]

/-- The comparison `Q (F K) ⟶ R(F) (Q K)` between the termwise image of a complex and the right
derived functor, induced by the unit of the right derived functor. It is an isomorphism on
K-injective complexes. -/
noncomputable def mapHomologicalComplexCompQToRightDerivedFunctor :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  (isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso D).symm ≪≫
    (associator _ _ _).symm ≪≫
    isoWhiskerRight (F.mapHomotopyCategoryFactors _).symm DerivedCategory.Qh ≪≫
    associator _ _ _).hom ≫
  whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ)) F.rightDerivedFunctorUnit ≫
  (associator _ _ _).inv ≫
  (isoWhiskerRight (DerivedCategory.quotientCompQhIso C) F.rightDerivedFunctor).hom

instance (I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso ((F.mapHomologicalComplexCompQToRightDerivedFunctor).app I) := by
  dsimp [mapHomologicalComplexCompQToRightDerivedFunctor]
  infer_instance

variable [Abelian.HasKInjectiveResolutions D] {J : Type*} [HasLimitsOfShape (Discrete J) C]
  [HasLimitsOfShape (Discrete J) D] [HasExactLimitsOfShape (Discrete J) D]
  [PreservesLimitsOfShape (Discrete J) F]

/-- **The unbounded right derived functor preserves products** (Stacks, Tag 08U1): if `C` has
K-injective resolutions and products of shape `J`, products of shape `J` in `D` are exact, and the
additive functor `F` preserves products of shape `J`, then `R(F) : D(C) ⥤ D(D)` preserves products
of shape `J`. -/
lemma preservesLimitsOfShape_discrete_rightDerivedFunctor :
    PreservesLimitsOfShape (Discrete J) F.rightDerivedFunctor := by
  have (K : J → DerivedCategory C) :
      PreservesLimit (Discrete.functor K) F.rightDerivedFunctor := by
    choose I hI e using fun b ↦ DerivedCategory.exists_iso_Q_obj_of_isKInjective (K b)
    have : PreservesLimit (Discrete.functor fun b ↦ DerivedCategory.Q.obj (I b))
        F.rightDerivedFunctor := by
      refine preservesLimit_of_preserves_limit_cone
        (DerivedCategory.isLimitFanMkQObjOfIsKInjective (productIsProduct I)) ?_
      refine (isLimitMapConeFanMkEquiv _ _ _).symm ?_
      let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
      have ht : IsLimit (Fan.mk (G.obj (∏ᶜ I)) fun b ↦ G.map (Pi.π I b)) :=
        isLimitFanMkObjOfIsLimit G I _ (productIsProduct I)
      have : (∏ᶜ I).IsKInjective := CochainComplex.isKInjective_of_isLimitFan (productIsProduct I)
      exact Fan.IsLimit.ofIsos (DerivedCategory.isLimitFanMkQObj ht)
        (fun b ↦ (asIso ((F.mapHomologicalComplexCompQToRightDerivedFunctor).app (I b))).symm)
        (asIso ((F.mapHomologicalComplexCompQToRightDerivedFunctor).app (∏ᶜ I))).symm
        (fun b ↦ by
          simpa using (F.mapHomologicalComplexCompQToRightDerivedFunctor).naturality
            (Pi.π I b))
    exact preservesLimit_of_iso_diagram _
      (Discrete.natIso fun b ↦ (e b.as).some.symm :
        Discrete.functor (fun b ↦ DerivedCategory.Q.obj (I b)) ≅ Discrete.functor K)
  exact preservesLimitsOfShape_of_discrete _

omit [HasLimitsOfShape (Discrete J) C] [HasLimitsOfShape (Discrete J) D]
  [HasExactLimitsOfShape (Discrete J) D] [PreservesLimitsOfShape (Discrete J) F] in
/-- **The unbounded right derived functor preserves derived inverse limits** (Stacks, Tag 08U1):
under the hypotheses of `preservesLimitsOfShape_discrete_rightDerivedFunctor` for countable
products, the triangulated functor `R(F)` sends a homotopy limit cone of a tower in `D(C)` (whose
legs fit into a Milnor triangle `R lim Kₙ ⟶ ∏ Kₙ ⟶ ∏ Kₙ ⟶ (R lim Kₙ)[1]`) to a homotopy limit cone
of the image tower. -/
lemma isHomotopyLimit_rightDerivedFunctor_mapCone [HasLimitsOfShape (Discrete ℕ) C]
    [HasLimitsOfShape (Discrete ℕ) D] [HasExactLimitsOfShape (Discrete ℕ) D]
    [PreservesLimitsOfShape (Discrete ℕ) F] {K : ℕᵒᵖ ⥤ DerivedCategory C} {c : Cone K}
    (hc : IsHomotopyLimit c) : IsHomotopyLimit (F.rightDerivedFunctor.mapCone c) :=
  have := F.preservesLimitsOfShape_discrete_rightDerivedFunctor (J := ℕ)
  hc.map _

end CategoryTheory.Functor
