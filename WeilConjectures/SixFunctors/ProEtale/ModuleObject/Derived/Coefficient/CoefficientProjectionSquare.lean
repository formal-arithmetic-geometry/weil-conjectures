/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRealization
import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

set_option linter.privateModule false

/-!
# Coefficient compatibility of the actual projection mate

Source: blueprint main-20261015, sk-thm-sfb-proper-base-change-rational.proof.md,
paragraph (3), projection on integral-model pairs before invertibility
(blueprint: lem-sfb-coefficient-projection-square).
-/

@[expose] public noncomputable section

set_option autoImplicit false

-- Keep the internal-Hom construction and the inverse image from the point opaque.
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open CategoryTheory.Abelian
open scoped CategoryTheory.Obj

universe v u₁ u₂ u₃ u₄
namespace CategoryTheory.Adjunction
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {A : Type u₁} {B : Type u₂} {B' : Type u₃} {C : Type u₄}
  [Category.{v} A] [Category.{v} B] [Category.{v} B'] [Category.{v} C]
  [Abelian A] [Abelian B] [Abelian B'] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions B']
  [Abelian.HasKInjectiveResolutions C]
  {F₁ : A ⥤ B} {F₂ : B ⥤ C} {G₁ : A ⥤ B'} {G₂ : B' ⥤ C}
  {U₁ : B ⥤ A} {U₂ : C ⥤ B} {V₁ : B' ⥤ A} {V₂ : C ⥤ B'}
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
  [U₁.Additive] [U₂.Additive] [V₁.Additive] [V₂.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [U₂.PreservesKInjectiveComplexes] [V₂.PreservesKInjectiveComplexes]
  (a₁ : F₁ ⊣ U₁) (a₂ : F₂ ⊣ U₂) (b₁ : G₁ ⊣ V₁) (b₂ : G₂ ⊣ V₂)

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [CategoryTheory.Abelian.HasKInjectiveResolutions D]
  (f : C ⥤ D) (g : D ⥤ C) [f.Additive] [g.Additive] [f.PreservesKFlatQuasiIso]

variable [PreservesFiniteLimits f] [PreservesFiniteColimits f]
set_option backward.defeqAttrib.useBackward true in
-- Exact left derivation transports the canonical adjunction along its counit comparison.
private lemma mapDerived_eq (adj : f ⊣ g) :
    adj.mapDerivedCategoryRightDerivedAdjunction =
      adj.derivedAdjunction.ofNatIsoLeft f.leftDerivedFunctorIsoMapDerivedCategory := by
  refine (adj.mapHomotopyCategory (.up ℤ)).derived_eq_ofNatIsoLeft
    (HomotopyCategory.quasiIso C (.up ℤ)) (HomotopyCategory.quasiIso D (.up ℤ)) _ _ _
    f.leftDerivedFunctorIsoMapDerivedCategory.symm ?_
  ext K
  simp only [Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← f.leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc]
end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction
variable {A B B' C : Type*} [Category A] [Category B] [Category B'] [Category C]
  {F₁ : A ⥤ B} {F₂ : B ⥤ C} {G₁ : A ⥤ B'} {G₂ : B' ⥤ C}
  {U₁ : B ⥤ A} {U₂ : C ⥤ B} {V₁ : B' ⥤ A} {V₂ : C ⥤ B'}
  (a₁ : F₁ ⊣ U₁) (a₂ : F₂ ⊣ U₂) (b₁ : G₁ ⊣ V₁) (b₂ : G₂ ⊣ V₂)
set_option backward.defeqAttrib.useBackward true in
-- Changing the exact right adjoints inserts their comparison at the two ends.
private lemma conjugate_right_transport {U₂' : C ⥤ B} {V₁' : B' ⥤ A}
    (r : U₂ ≅ U₂') (s : V₁ ≅ V₁') (t : G₁ ⋙ G₂ ⟶ F₁ ⋙ F₂) :
    conjugateEquiv (a₁.comp (a₂.ofNatIsoRight r))
        ((b₁.ofNatIsoRight s).comp b₂) t =
      Functor.whiskerRight r.inv U₁ ≫
        conjugateEquiv (a₁.comp a₂) (b₁.comp b₂) t ≫
        Functor.whiskerLeft V₂ s.hom := by
  ext K
  simp only [conjugateEquiv_apply_app, comp_unit_app, comp_counit_app,
    ofNatIsoRight_unit, ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
    Functor.comp_map, Category.assoc]
  simp only [← V₁'.map_comp]
  erw [← s.hom.naturality]
  erw [b₁.unit.naturality_assoc]
  simp only [Functor.comp_map]
  simp only [← V₁.map_comp_assoc]
  congr 2
  erw [b₂.unit.naturality_assoc]
  simp only [Functor.comp_map, ← V₂.map_comp]
  congr 2
  erw [t.naturality_assoc]
  simp only [Functor.comp_map]
  congr 1
  simp only [← F₂.map_comp_assoc]
  have hn := a₁.counit.naturality (r.inv.app K)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [← hn]
  rfl
set_option backward.defeqAttrib.useBackward true in
-- Conjugation is natural in all four left adjoints.
private lemma conjugate_left_transport
    {F₁' : A ⥤ B} {F₂' : B ⥤ C} {G₁' : A ⥤ B'} {G₂' : B' ⥤ C}
    (e₁ : F₁ ≅ F₁') (e₂ : F₂ ≅ F₂') (d₁ : G₁ ≅ G₁') (d₂ : G₂ ≅ G₂')
    (t : G₁' ⋙ G₂' ⟶ F₁' ⋙ F₂') :
    conjugateEquiv ((a₁.ofNatIsoLeft e₁).comp (a₂.ofNatIsoLeft e₂))
        ((b₁.ofNatIsoLeft d₁).comp (b₂.ofNatIsoLeft d₂)) t =
      conjugateEquiv (a₁.comp a₂) (b₁.comp b₂)
        (Functor.whiskerRight d₁.hom G₂ ≫ Functor.whiskerLeft G₁' d₂.hom ≫ t ≫
          Functor.whiskerLeft F₁' e₂.inv ≫ Functor.whiskerRight e₁.inv F₂) := by
  ext K
  simp only [conjugateEquiv_apply_app, comp_unit_app, comp_counit_app,
    ofNatIsoLeft_unit, ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
    Functor.comp_map, Category.assoc]
  simp only [← V₁.map_comp]
  erw [b₂.unit.naturality_assoc]
  simp only [Functor.comp_map, ← V₂.map_comp]
  congr 2
  erw [e₂.inv.naturality_assoc]
  erw [e₂.inv.naturality_assoc]
  rfl
end CategoryTheory.Adjunction

namespace CategoryTheory.Functor
variable {A : Type u₁} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A]
  [BraidedCategory A] [HasFunctorialFlatResolution A]
variable {B : Type u₂} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalClosed B]
  [BraidedCategory B] [HasFunctorialFlatResolution B]
variable {B' : Type u₃} [Category.{u + 1} B'] [Abelian B']
  [IsGrothendieckAbelian.{u + 1} B']
  [MonoidalCategory B'] [MonoidalPreadditive B'] [MonoidalClosed B']
  [BraidedCategory B'] [HasFunctorialFlatResolution B']
variable {C : Type u₄} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
variable (F₁ : A ⥤ B) (F₂ : B ⥤ C) (G₁ : A ⥤ B') (G₂ : B' ⥤ C)
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
set_option backward.defeqAttrib.useBackward true in
-- The composite left-derived square is the levelwise square in exact coordinates.
private lemma left_path_comparison (t : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂) :
    whiskerRight G₁.leftDerivedFunctorIsoMapDerivedCategory.hom G₂.leftDerivedFunctor ≫
      whiskerLeft G₁.mapDerivedCategory G₂.leftDerivedFunctorIsoMapDerivedCategory.hom ≫
      (mapDerivedCategorySquareIso t).hom ≫
      whiskerLeft F₁.mapDerivedCategory F₂.leftDerivedFunctorIsoMapDerivedCategory.inv ≫
      whiskerRight F₁.leftDerivedFunctorIsoMapDerivedCategory.inv F₂.leftDerivedFunctor =
    ((G₁.leftDerivedFunctorCompIso G₂).symm ≪≫
      (G₁ ⋙ G₂).leftDerivedFunctorNatIso t ≪≫ F₁.leftDerivedFunctorCompIso F₂).hom := by
  ext K
  simp only [leftDerivedFunctorNatIso, leftDerivedFunctorCompIso,
    mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    isoWhiskerLeft_inv, isoWhiskerRight_inv, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [← F₂.leftDerivedFunctorIsoMapDerivedCategory.inv.naturality]
  rw [G₂.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
end CategoryTheory.Functor

namespace CategoryTheory.Functor
variable {A : Type u₁} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A]
  [BraidedCategory A] [HasFunctorialFlatResolution A]
variable {B : Type u₂} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalClosed B]
  [BraidedCategory B] [HasFunctorialFlatResolution B]
variable {B' : Type u₃} [Category.{u + 1} B'] [Abelian B']
  [IsGrothendieckAbelian.{u + 1} B']
  [MonoidalCategory B'] [MonoidalPreadditive B'] [MonoidalClosed B']
  [BraidedCategory B'] [HasFunctorialFlatResolution B']
variable {C : Type u₄} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
variable (F₁ : A ⥤ B) (F₂ : B ⥤ C) (G₁ : A ⥤ B') (G₂ : B' ⥤ C)
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {U₁ : B ⥤ A} {U₂ : C ⥤ B} {V₁ : B' ⥤ A} {V₂ : C ⥤ B'}
  [U₁.Additive] [U₂.Additive] [V₁.Additive] [V₂.Additive]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits V₁] [PreservesFiniteColimits V₁]
  [U₂.PreservesKInjectiveComplexes] [V₂.PreservesKInjectiveComplexes]
  (a₁ : F₁ ⊣ U₁) (a₂ : F₂ ⊣ U₂) (b₁ : G₁ ⊣ V₁) (b₂ : G₂ ⊣ V₂)

end CategoryTheory.Functor

set_option backward.defeqAttrib.useBackward true in
private theorem push_eq_mate_pull_inv
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {T : A ⥤ B} {S : B ⥤ A} {T' : A' ⥤ B'} {S' : B' ⥤ A'}
    {l : A' ⥤ A} {r : A ⥤ A'} {l' : B' ⥤ B} {r' : B ⥤ B'}
    (a : T ⊣ S) (b : T' ⊣ S') (c : l ⊣ r) (d : l' ⊣ r')
    (e : r' ⋙ S' ≅ S ⋙ r) :
    Adjunction.pushHomOfComapIso a b e =
      (mateEquiv c d (TwoSquare.mk _ _ _ _
        (Adjunction.pullIsoOfComapIso a b c d e).inv)).natTrans := by
  have h := iterated_mateEquiv_conjugateEquiv_symm c d b a
    (TwoSquare.mk _ _ _ _ e.inv)
  apply (TwoSquare.equivNatTrans _ _ _ _).symm.injective
  apply (mateEquiv c d).symm.injective
  change (mateEquiv c d).symm ((mateEquiv a b).symm (.mk _ _ _ _ e.inv)) =
    (mateEquiv c d).symm
      (mateEquiv c d (.mk _ _ _ _ (Adjunction.pullIsoOfComapIso a b c d e).inv))
  rw [Equiv.symm_apply_apply]
  exact h

-- Preserve the concrete geometric functors while checking the abstract identities.
attribute [local irreducible] AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.lowerStar

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

-- Do not expand the canonical comparisons during tactic matching.
attribute [local irreducible]
  AlgebraicGeometry.ProEtale.CondensedRing.coefficientScalarPathIso

end AlgebraicGeometry.ProEtale.CondensedRing
