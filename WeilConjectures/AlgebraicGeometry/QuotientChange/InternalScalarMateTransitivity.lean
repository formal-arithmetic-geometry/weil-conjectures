/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # Successive internal scalar mates and normalized units

Source: blueprint main-20261015, integral proper-base-change proof, paragraph (3);
Stacks Project, Tags 0D6D, 0G7E and 07A6
(blueprint: lem-sfb-internal-scalar-mate-transitivity).

All functors are the specified ordinary unbounded internal-module functors.
The scalar associator is normalized by its universal computation counits.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  HasDerivedCategory.standard

universe u u₀ u₁ u₂ u₃ u₄ u₅ u₆ v₀ v₁ v₂ v₃ v₄ v₅ v₆ w₀ w₁ w₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
  [MonObj Λ₂] [IsCommMonObj Λ₂]

/-- The canonical comparison for successive exact scalar restrictions. It comes from
ordinary restriction, whose underlying module maps are identities, and localization.
Source: Stacks 07A6 (blueprint: lem-sfb-internal-scalar-mate-transitivity). -/
def scalarRestrictionComp (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (b : Λ₁ ⟶ Λ₂) [IsMonHom b] (T : Scheme.{u}) :
    V b T ⋙ V a T ≅ V (a ≫ b) T :=
  (Functor.mapDerivedCategoryCompIso (V₀ b T) (V₀ a T)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Mod.comapComp (coefficientMap a T) (coefficientMap b T)).symm ≪≫
        Mod.comapCongr (coefficientMap_comp a b T).symm)

attribute [local irreducible] scalarRestrictionComp
  scalarAdj Mod.extendRestrictAdjunction CondensedRing.upperStarLowerStarAdjunction
  Functor.leftDerivedFunctorCounit Functor.rightDerivedFunctorUnit

attribute [local irreducible] scalarCounit pullCounit

private def rawAdj (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}} [MonObj R] [MonObj S] [IsCommMonObj R]
    (a : R ⟶ S) [IsMonHom a] : Mod.extendScalars a ⊣ Mod.comap a := by
  let C := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}
  let hl : ∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z) :=
    ProEtale.preservesColimitsOfSize_tensorLeft_sheaf Ab.{u + 1} T
  let hr : ∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z) :=
    ProEtale.preservesColimitsOfSize_tensorRight_sheaf Ab.{u + 1} T
  exact @Mod.extendRestrictAdjunction.{u + 1, u + 2} C _ _ _ hl hr _ R S _ _ _ a _

private def ordinaryAdj (a : Λ₀ ⟶ Λ₁) [IsMonHom a] (T : Scheme.{u}) :
    extension a T ⊣ V₀ a T := rawAdj T (coefficientMap a T)

section GeneralDerived

variable {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions E]

end GeneralDerived

attribute [local irreducible] ordinaryAdj rawAdj ordinaryComp

private def resOrd (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (b : Λ₁ ⟶ Λ₂) [IsMonHom b] (T : Scheme.{u}) :
    V₀ b T ⋙ V₀ a T ≅ V₀ (a ≫ b) T :=
  (Mod.comapComp (coefficientMap a T) (coefficientMap b T)).symm ≪≫
    Mod.comapCongr (coefficientMap_comp a b T).symm

omit [IsCommMonObj Λ₁] in
private def scalarComp (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (b : Λ₁ ⟶ Λ₂) [IsMonHom b] (T : Scheme.{u}) :
    D a T ⋙ D b T ≅ D (a ≫ b) T :=
  (((scalarAdj a T).comp (scalarAdj b T)).ofNatIsoRight
    (scalarRestrictionComp a b T)).leftAdjointUniq (scalarAdj (a ≫ b) T)

attribute [local irreducible] scalarComp

section ExactComposition

private local instance exact_comp_limits {A B E : Type*}
    [Category A] [Category B] [Category E] (F : A ⥤ B) (G : B ⥤ E)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    PreservesFiniteLimits (F ⋙ G) := comp_preservesFiniteLimits F G

private local instance exact_comp_colimits {A B E : Type*}
    [Category A] [Category B] [Category E] (F : A ⥤ B) (G : B ⥤ E)
    [PreservesFiniteColimits F] [PreservesFiniteColimits G] :
    PreservesFiniteColimits (F ⋙ G) := comp_preservesFiniteColimits F G

end ExactComposition

section NormalizedComposition
variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  {DA : Type u₄} {DB : Type u₅} {DC : Type u₆}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Category.{v₄} DA] [Category.{v₅} DB] [Category.{v₆} DC]
  {F : A ⥤ B} {R : B ⥤ A} {G : B ⥤ C} {S : C ⥤ B}
  {FD : DA ⥤ DB} {RD : DB ⥤ DA} {GD : DB ⥤ DC} {SD : DC ⥤ DB}
  {QA : A ⥤ DA} {QB : B ⥤ DB} {QC : C ⥤ DC}

end NormalizedComposition

attribute [local irreducible] resOrd CondensedRing.pullIso

attribute [local irreducible] Functor.mapHomotopyCategoryCompIso
  Functor.mapHomotopyCategoryIdIso Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryIdIso
  NatTrans.mapHomotopyCategory

attribute [local irreducible] rho

end AlgebraicGeometry.ProEtale.QuotientChange
