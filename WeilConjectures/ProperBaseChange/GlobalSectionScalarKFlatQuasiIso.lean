/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ring.RingHomExtensionDefsSupplement
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.Ring.RingHomExtensionDefsSupplement
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.Ring.RingHomExtensionTransportSupplement
import Mathlib.Algebra.Homology.Functor

/-! # Scalar extension from global sections on K-flat quasi-isomorphisms

Source: Stacks Project, Cohomology on Sites, Tags 06YS and 06YT; algebraization.tex,
Tag 099E, final paragraph.
(blueprint: lem-weil-pbc-global-section-scalar-kflat-quasi-iso).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace CategoryTheory

attribute [local instance] ringFamilyGlobalExtension_additive

/- The tensor-presheaf construction generalizes the proved private construction in
`WeilConjectures.CategoryTheory.PresheafChangeOfRingsAdjunction` from open sets to an
arbitrary small category. Keeping both ring presheaves explicit avoids expanding the
abstract pullback while elaborating the comparison. -/
section TensorPresheaf
variable {D : Type u} [SmallCategory D]
variable (R S : Dᵒᵖ ⥤ CommRingCat.{u})
variable (α : R ⟶ S)
local notation "a" => Functor.whiskerRight α (forget₂ CommRingCat RingCat)
local notation "push" => PresheafOfModules.pushforward
  (R := S ⋙ forget₂ CommRingCat RingCat) (S := R ⋙ forget₂ CommRingCat RingCat)
  (F := 𝟭 D) a
local notation "pull" => PresheafOfModules.pullback
  (R := S ⋙ forget₂ CommRingCat RingCat) (S := R ⋙ forget₂ CommRingCat RingCat)
  (F := 𝟭 D) a
local notation "adjP" => PresheafOfModules.pullbackPushforwardAdjunction
  (R := S ⋙ forget₂ CommRingCat RingCat) (S := R ⋙ forget₂ CommRingCat RingCat)
  (F := 𝟭 D) a
open scoped ChangeOfRings TensorProduct

private noncomputable def tensorRestriction (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
    {U V : Dᵒᵖ} (i : U ⟶ V) :
    (ModuleCat.extendScalars (α.app U).hom).obj (M.obj U) ⟶
      (ModuleCat.restrictScalars (S.map i).hom).obj
        ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V)) := by
  let : Module (R.obj V) (S.obj V) :=
    Module.compHom (S.obj V) (α.app V).hom
  let T := (ModuleCat.restrictScalars (S.map i).hom).obj
    ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V))
  let h : M.obj U ⟶ (ModuleCat.restrictScalars (α.app U).hom).obj T :=
    ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (α.app U).hom).obj T)
      { toFun := fun m ↦ (1 : S.obj V) ⊗ₜ[R.obj V,
          (α.app V).hom] M.map i m
        map_add' := by
          intro m n
          rw [map_add, TensorProduct.tmul_add]
        map_smul' := by
          intro r m
          change (1 : S.obj V) ⊗ₜ[R.obj V, (α.app V).hom]
            M.map i (r • m) = S.map i (α.app U r) •
              ((1 : S.obj V) ⊗ₜ[R.obj V, (α.app V).hom] M.map i m)
          rw [M.map_smul]
          have hn : S.map i (α.app U r) =
              α.app V (R.map i r) :=
            ConcreteCategory.congr_hom (α.naturality i).symm r
          rw [hn]
          change (1 : S.obj V) ⊗ₜ[R.obj V]
            ((R.map i r) • (show M.obj V from M.map i m)) = _
          rw [TensorProduct.tmul_smul]
          rfl }
  exact ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    («R» := R.obj U) («S» := S.obj U) (α.app U).hom h

private theorem tensorRestriction_tmul (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
    {U V : Dᵒᵖ} (i : U ⟶ V)
    (b : S.obj U) (m : M.obj U) :
    tensorRestriction R S α M i (b ⊗ₜ[R.obj U, (α.app U).hom] m) =
      S.map i b ⊗ₜ[R.obj V, (α.app V).hom] M.map i m := by
  let : Module (R.obj V) (S.obj V) :=
    Module.compHom (S.obj V) (α.app V).hom
  let T := (ModuleCat.restrictScalars (S.map i).hom).obj
    ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V))
  let : Module (R.obj U) T := Module.compHom T (α.app U).hom
  let : Module (R.obj U) (S.obj U) :=
    Module.compHom (S.obj U) (α.app U).hom
  unfold tensorRestriction
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  change S.map i b •
    ((1 : S.obj V) ⊗ₜ[R.obj V, (α.app V).hom] M.map i m) = _
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]

private noncomputable def tensorPresheaf (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    PresheafOfModules.{u} (S ⋙ forget₂ _ _) where
  obj U := (ModuleCat.extendScalars (α.app U).hom).obj (M.obj U)
  map i := tensorRestriction R S α M i
  map_id U := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    rw [tensorRestriction_tmul]
    simp
    rfl
  map_comp {U V W} i j := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    simp only [ModuleCat.comp_apply, tensorRestriction_tmul]
    change _ = tensorRestriction R S α M j _
    erw [tensorRestriction_tmul]
    simp
    rfl

private noncomputable def tensorToRestrict
    (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (N : PresheafOfModules.{u} (S ⋙ forget₂ _ _))
    (f : tensorPresheaf R S α M ⟶ N) : M ⟶ (PresheafOfModules.restrictScalars a).obj N where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
    (α.app U).hom (f.app U)
  naturality := by
    intro U V i
    ext m
    change f.app V ((1 : S.obj V) ⊗ₜ[R.obj V,
      (α.app V).hom] M.map i m) =
      N.map i (f.app U ((1 : S.obj U) ⊗ₜ[R.obj U,
        (α.app U).hom] m))
    rw [← PresheafOfModules.naturality_apply f i]
    change _ = f.app V (tensorRestriction R S α M i _)
    rw [tensorRestriction_tmul]
    simp

private noncomputable def tensorFromRestrict
    (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (N : PresheafOfModules.{u} (S ⋙ forget₂ _ _))
    (g : M ⟶ (PresheafOfModules.restrictScalars a).obj N) : tensorPresheaf R S α M ⟶ N where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    («R» := R.obj U) («S» := S.obj U) (α.app U).hom (g.app U)
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      («R» := R.obj V) («S» := S.obj V) (α.app V).hom (g.app V)
        (tensorRestriction R S α M i _) =
      N.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        («R» := R.obj U) («S» := S.obj U) (α.app U).hom (g.app U) _)
    rw [tensorRestriction_tmul]
    simp only [map_one]
    let : Module (R.obj V) (S.obj V) :=
      Module.compHom (S.obj V) (α.app V).hom
    let : Module (R.obj V) (N.obj V) :=
      Module.compHom (N.obj V) (α.app V).hom
    let : Module (R.obj U) (S.obj U) :=
      Module.compHom (S.obj U) (α.app U).hom
    let : Module (R.obj U) (N.obj U) :=
      Module.compHom (N.obj U) (α.app U).hom
    erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      («R» := R.obj V) («S» := S.obj V), TensorProduct.lift.tmul,
      ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      («R» := R.obj U) («S» := S.obj U), TensorProduct.lift.tmul]
    change (1 : S.obj V) • (show N.obj V from g.app V (M.map i m)) =
      N.map i ((1 : S.obj U) • (show N.obj U from g.app U m))
    simp only [one_smul]
    exact PresheafOfModules.naturality_apply g i m

private noncomputable def tensorHomEquiv
    (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (N : PresheafOfModules.{u} (S ⋙ forget₂ _ _)) :
    (tensorPresheaf R S α M ⟶ N) ≃ (M ⟶ (PresheafOfModules.restrictScalars a).obj N) where
  toFun := tensorToRestrict R S α M N
  invFun := tensorFromRestrict R S α M N
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (α.app U).hom).left_inv _
  right_inv g := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (α.app U).hom).right_inv _

private noncomputable def tensorFunctor :
    PresheafOfModules.{u} (R ⋙ forget₂ _ _) ⥤
      PresheafOfModules.{u} (S ⋙ forget₂ _ _) :=
  Adjunction.leftAdjointOfEquiv (tensorHomEquiv R S α) (by intros; rfl)

end TensorPresheaf

end CategoryTheory
