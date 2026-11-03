/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.InternalBar.CondensedInternalBarResolution
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit

/-! # Cancelling scalar restriction along an isomorphism

Source: the scalar-extension equivalence in
`WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit`;
Stacks Project Tag 03D8, the coefficient transport used in the point compositor.
(blueprint: new-c1-profinite-free-slice-point-cancellation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
universe v w z
section Cancellation
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
  (α : R ⟶ S) [IsMonHom α] [IsIso α]
  {A : Type w} [Category.{z} A]
  (F : A ⥤ Mod C R) (G : A ⥤ Mod C S) (m : F ≅ G ⋙ Mod.comap α)

/-- Cancellation of scalar restriction along an isomorphism.
Source: the scalar-extension equivalence and its unit in
`WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit`.
Proof: whisker the given comparison by extension of scalars, reassociate,
then cancel scalar restriction using the coefficient-isomorphism equivalence.
Naturality moves the scalar-extension comparison before the given map, and
its identity underlying unit gives the component formula.
(blueprint: new-c1-profinite-free-slice-point-cancellation). -/
theorem profiniteFreeSlice_exists_cancel :
    ∃ e : F ⋙ Mod.extendScalars α ≅ G,
      ∀ a : A, (e.hom.app a).hom =
        ((Mod.extendScalarsIsoComapInv α).hom.app (F.obj a)).hom ≫
          (m.hom.app a).hom := by
  let e : F ⋙ Mod.extendScalars α ≅ G :=
    Functor.isoWhiskerRight m _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft G
        (Functor.isoWhiskerLeft _ (Mod.extendScalarsIsoComapInv α) ≪≫
          (Mod.comapEquivalenceOfIsIso α).unitIso.symm) ≪≫ Functor.rightUnitor _
  refine ⟨e, ?_⟩
  intro a
  have hn := congrArg (fun k ↦ k.hom)
    ((Mod.extendScalarsIsoComapInv α).hom.naturality (m.hom.app a))
  simp only [Mod.comp_hom'] at hn
  simp only [e, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.rightUnitor_hom_app, Mod.comp_hom', Mod.id_hom', Category.id_comp]
  erw [Category.comp_id]
  erw [← Category.assoc, hn, Mod.comapEquivalenceOfIsIso_unitIso_inv_app_hom,
    Category.comp_id]
  rfl

end Cancellation


end AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
