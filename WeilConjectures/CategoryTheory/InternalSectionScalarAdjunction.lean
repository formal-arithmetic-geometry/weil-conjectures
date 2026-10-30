/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.ScalarInternalHomData
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Scalar adjunctions under section reconstruction

Source: Stacks Project, Modules on Sites, Tags 03EK and 0GMW; Cohomology on Sites,
Tags 06YS, 06YY and 07A6; Derived Categories, Tag 09T5; blueprint main-20261015,
det-prop-scalar-six-pullback.proof.md, (1), first paragraph
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u c v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings

-- Upstream made these instances local (InternalSectionTensorComparison, SheafTensor).
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
attribute [local instance] sfbSheafTensor_monoidalPreadditive sfbSheafTensor_hasWeakSheafify
attribute [instance] SheafOfModules.ScalarDerivedPair.extension_additive

namespace CategoryTheory.InternalAbelianSheafModule

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [UnivLE.{max c v, u}] [HasSheafify J AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]

/-- The section-ring map reconstructed from the specified internal ring map.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
def sectionScalarMap {R S : Sheaf J AddCommGrpCat.{u}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] : sectionRingSheaf J R ⟶ sectionRingSheaf J S :=
  ⟨Functor.whiskerRight
    ((Monoidal.commMonFunctorCategoryEquivalence Cᵒᵖ AddCommGrpCat.{u}).functor.map
      ((sheafToPresheaf J AddCommGrpCat.{u}).mapCommMon.map
        (CommMon.homMk (A := CommMon.mk R) (B := CommMon.mk S) (Mon.Hom.mk' a)))) commMonToRing⟩

variable {R S : Sheaf J AddCommGrpCat.{u}}
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]

/-- Internal modules for the scalar comparison; this is the recorded module category.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
abbrev scalarInternalModules (T : Sheaf J AddCommGrpCat.{u}) [MonObj T] :=
  Mod (Sheaf J AddCommGrpCat.{u}) T

variable [HasDerivedCategory.{w} (scalarInternalModules J R)]
  [HasDerivedCategory.{w} (scalarInternalModules J S)]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J R))]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J S))]

open SheafOfModules

private noncomputable def scalarRestrictionIso :
    Mod.comap a ⋙ (sectionModuleEquivalence J R).functor ≅
      (sectionModuleEquivalence J S).functor ⋙
        SheafOfModules.scalarRestriction (sectionScalarMap J a) := by
  refine NatIso.ofComponents (fun N ↦ ?_) ?_
  · let h : ∀ (U : Cᵒᵖ) (r : R.obj.obj U) (x : N.X.obj.obj U),
        (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) R N.X).app U) ≫
          ((a ▷ N.X).hom.app U) ≫ ((Mod.act N.X).hom.app U)) (r ⊗ₜ[ℤ] x) =
        (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) S N.X).app U) ≫
          ((Mod.act N.X).hom.app U)) ((a.hom.app U r) ⊗ₜ[ℤ] x) := by
      intro U r x
      have hμ := congr_app (Functor.LaxMonoidal.μ_natural_left
        (sheafToPresheaf J AddCommGrpCat.{u}) a N.X) U
      have hh := ConcreteCategory.congr_hom
        (congrArg (fun f ↦ f ≫ (Mod.act N.X).hom.app U) hμ) (r ⊗ₜ[ℤ] x)
      exact hh.symm
    let f : ((sectionModuleEquivalence J R).functor.obj ((Mod.comap a).obj N)) ⟶
        (SheafOfModules.scalarRestriction (sectionScalarMap J a)).obj
          ((sectionModuleEquivalence J S).functor.obj N) :=
      ⟨{ app := fun U ↦ ModuleCat.ofHom
          (X := ((sectionModuleEquivalence J R).functor.obj ((Mod.comap a).obj N)).val.obj U)
          (Y := ((SheafOfModules.scalarRestriction (sectionScalarMap J a)).obj
            ((sectionModuleEquivalence J S).functor.obj N)).val.obj U)
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun r x ↦ h U r x }
         naturality := by intros; ext x; rfl }⟩
    let g : (SheafOfModules.scalarRestriction (sectionScalarMap J a)).obj
          ((sectionModuleEquivalence J S).functor.obj N) ⟶
        ((sectionModuleEquivalence J R).functor.obj ((Mod.comap a).obj N)) :=
      ⟨{ app := fun U ↦ ModuleCat.ofHom
          (X := ((SheafOfModules.scalarRestriction (sectionScalarMap J a)).obj
            ((sectionModuleEquivalence J S).functor.obj N)).val.obj U)
          (Y := ((sectionModuleEquivalence J R).functor.obj ((Mod.comap a).obj N)).val.obj U)
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun r x ↦ (h U r x).symm }
         naturality := by intros; ext x; rfl }⟩
    exact ⟨f, g, by ext U x; rfl, by ext U x; rfl⟩
  · intro N N' f
    ext U x
    rfl

omit [UnivLE.{max c v, u}] in
private theorem inverseMate_isIso
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {U : B ⥤ A} {F : D ⥤ E} {V : E ⥤ D}
    {G : A ⥤ D} {H : B ⥤ E} [G.IsEquivalence] [H.IsEquivalence]
    (adj : L ⊣ U) (adj' : F ⊣ V) (β : U ⋙ G ≅ H ⋙ V) :
    IsIso (((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ β.hom)).natTrans) := by
  let α := ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ β.hom)).natTrans
  let βop : TwoSquare H.op U.op V.op G.op := TwoSquare.mk _ _ _ _ (NatTrans.op β.hom)
  have hi := isIso_mateEquiv_of_isEquivalence adj.op adj'.op βop
  have he : (NatTrans.op α) = (mateEquiv adj.op adj'.op βop).natTrans := by
    ext X
    simp [α, βop, mateEquiv]
  have : IsIso (NatTrans.op α) := by rw [he]; exact hi
  have (X : A) : IsIso (α.app X) := by
    have hX : IsIso ((α.app X).op) :=
      NatIso.isIso_app_of_isIso (NatTrans.op α) (Opposite.op X)
    exact isIso_of_op (α.app X)
  exact NatIso.isIso_of_isIso_app α

end CategoryTheory.InternalAbelianSheafModule
