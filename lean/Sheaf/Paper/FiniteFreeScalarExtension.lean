/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Sheaf.Algebra.Homology.ChangeOfRingsComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Paper.FinitePowerComplex
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Basis coordinates for finite free extension of sheaves

Source: Stacks Project, Modules on Sites, Tags 03CY and 03EK;
Bhatt--Scholze, Lemma 3.4.12.
(blueprint: lem-pur-finite-free-scalar-extension).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] CategoryTheory.Limits.limit

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace SheafOfModules
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R S : Sheaf J CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡" T => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T
set_option hygiene false in
local notation "𝓻" φ => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ

@[irreducible] private def sectionProductIso (d : ℕ) (M : SheafOfModules.{u} (𝓡 R)) (V : Cᵒᵖ) :
    (∏ᶜ fun _ : Fin d ↦ M).val.obj V ≅ ModuleCat.of (R.obj.obj V)
      (Fin d → M.val.obj V) :=
  PreservesProduct.iso (evaluation (𝓡 R) V) (fun _ : Fin d ↦ M) ≪≫
    ModuleCat.piIsoPi (fun _ : Fin d ↦ M.val.obj V)

private theorem sectionProductIso_apply (d : ℕ) (M : SheafOfModules.{u} (𝓡 R))
    (V : Cᵒᵖ) (x : (∏ᶜ fun _ : Fin d ↦ M).val.obj V) (i : Fin d) :
    (sectionProductIso d M V).hom x i = (Pi.π (fun _ : Fin d ↦ M) i).val.app V x := by
  let E := evaluation (𝓡 R) V
  let f := fun _ : Fin d ↦ M
  let q : ModuleCat.of (R.obj.obj V) (Fin d → M.val.obj V) ⟶ M.val.obj V :=
    ModuleCat.ofHom (LinearMap.proj i)
  have h : (sectionProductIso d M V).hom ≫ q = (Pi.π f i).val.app V := by
    unfold sectionProductIso
    exact (Category.assoc (PreservesProduct.iso E f).hom
      (ModuleCat.piIsoPi (fun _ : Fin d ↦ M.val.obj V)).hom q).trans
      ((congrArg (fun g ↦ (PreservesProduct.iso E f).hom ≫ g)
        (ModuleCat.piIsoPi_hom_ker_subtype (fun _ : Fin d ↦ M.val.obj V) i)).trans
        (piComparison_comp_π E f i))
  exact congrArg (fun g ↦ g x) h

@[irreducible] private def sectionBasis (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S))) (V : Cᵒᵖ) :
    ((restrictScalars (𝓻 φ)).obj (unit (𝓡 S))).val.obj V ≃ₗ[R.obj.obj V]
      (Fin d → R.obj.obj V) :=
  ((evaluation (𝓡 R) V).mapIso e.symm ≪≫ sectionProductIso d (unit (𝓡 R)) V).toLinearEquiv

@[irreducible] private def scalarExtensionApp (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) (V : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars (𝓻 φ).hom).obj
      (changeOfRingsPresheaf.{u, u, u} φ M)).obj V ≅ (∏ᶜ fun _ : Fin d ↦ M).val.obj V := by
  let A := R.obj.obj V
  let B := S.obj.obj V
  let ρ := (φ.hom.app V).hom
  let : Algebra A B := ρ.toAlgebra
  exact (TensorProduct.congr (sectionBasis φ d e V) (LinearEquiv.refl A (M.val.obj V)) ≪≫ₗ
    TensorProduct.comm A (Fin d → A) (M.val.obj V) ≪≫ₗ
    TensorProduct.piScalarRight A A (M.val.obj V) (Fin d)).toModuleIso ≪≫
      (sectionProductIso d M V).symm

private theorem scalarExtensionApp_tmul (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) (V : Cᵒᵖ)
    (s : S.obj.obj V) (m : M.val.obj V) (i : Fin d) :
    (Pi.π (fun _ : Fin d ↦ M) i).val.app V
      ((scalarExtensionApp φ d e M V).hom (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)) =
      ((e.inv ≫ Pi.π (fun _ : Fin d ↦ unit (𝓡 R)) i).val.app V s) • m := by
  rw [← sectionProductIso_apply]
  unfold scalarExtensionApp
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  erw [← ModuleCat.comp_apply, Category.assoc, Iso.inv_hom_id]
  change (TensorProduct.piScalarRight (R.obj.obj V) (R.obj.obj V)
      (M.val.obj V) (Fin d)) (m ⊗ₜ[R.obj.obj V] (sectionBasis φ d e V s)) i = _
  change (TensorProduct.piScalarRightHom (R.obj.obj V) (R.obj.obj V)
      (M.val.obj V) (Fin d)) (m ⊗ₜ[R.obj.obj V] (sectionBasis φ d e V s)) i = _
  have h := congrArg (fun f ↦ f i)
    (TensorProduct.piScalarRightHom_tmul (R.obj.obj V) (R.obj.obj V)
      (M.val.obj V) (Fin d) m (sectionBasis φ d e V s))
  rw [h]
  apply congrArg (fun r ↦ r • m)
  unfold sectionBasis
  exact sectionProductIso_apply d (unit (𝓡 R)) V _ i

private theorem sectionProduct_ext (d : ℕ) (M : SheafOfModules.{u} (𝓡 R))
    (V : Cᵒᵖ) (x y : (∏ᶜ fun _ : Fin d ↦ M).val.obj V)
    (h : ∀ i : Fin d, (Pi.π (fun _ : Fin d ↦ M) i).val.app V x =
      (Pi.π (fun _ : Fin d ↦ M) i).val.app V y) : x = y := by
  apply (sectionProductIso d M V).toLinearEquiv.injective
  funext i
  change (sectionProductIso d M V).hom x i = (sectionProductIso d M V).hom y i
  rw [sectionProductIso_apply, sectionProductIso_apply]
  exact h i

private theorem changeMap_tmul (φ : R ⟶ S) (M : SheafOfModules.{u} (𝓡 R))
    {V W : Cᵒᵖ} (f : V ⟶ W) (s : S.obj.obj V) (m : M.val.obj V) :
    changeOfRingsMap φ M f (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m) =
      S.obj.map f s ⊗ₜ[R.obj.obj W, (φ.hom.app W).hom] M.val.map f m :=
  Classical.choose_spec (exists_changeOfRingsMap φ M f) s m

@[irreducible] private def scalarExtensionPresheafIso (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) :
    (PresheafOfModules.restrictScalars (𝓻 φ).hom).obj (changeOfRingsPresheaf.{u, u, u} φ M) ≅
      (∏ᶜ fun _ : Fin d ↦ M).val :=
  PresheafOfModules.isoMk (scalarExtensionApp φ d e M) (by
    intro V W f
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
      apply sectionProduct_ext d M W
      intro i
      change (Pi.π (fun _ : Fin d ↦ M) i).val.app W
          ((scalarExtensionApp φ d e M W).hom (changeOfRingsMap φ M f
            (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m))) =
        (Pi.π (fun _ : Fin d ↦ M) i).val.app W
          ((∏ᶜ fun _ : Fin d ↦ M).val.map f
            ((scalarExtensionApp φ d e M V).hom
              (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)))
      have ht := congrArg ((Pi.π (fun _ : Fin d ↦ M) i).val.app W ∘
        (scalarExtensionApp φ d e M W).hom) (changeMap_tmul φ M f s m)
      exact ht.trans ((scalarExtensionApp_tmul φ d e M W _ _ i).trans (by
        have hπ := PresheafOfModules.naturality_apply
          (Pi.π (fun _ : Fin d ↦ M) i).val f
          ((scalarExtensionApp φ d e M V).hom
            (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m))
        have hc := scalarExtensionApp_tmul φ d e M V s m i
        have hl := PresheafOfModules.map_smul M.val f
          (((e.inv ≫ Pi.π (fun _ : Fin d ↦ unit (𝓡 R)) i).val.app V) s) m
        have hb := PresheafOfModules.naturality_apply
          (e.inv ≫ Pi.π (fun _ : Fin d ↦ unit (𝓡 R)) i).val f s
        exact (congrArg (fun r ↦ r • M.val.map f m) hb).trans
          (hl.symm.trans ((congrArg (M.val.map f) hc).symm.trans hπ.symm)))))

@[irreducible] private def restrictSheafifyHom {A B : Sheaf J RingCat.{u}} (φ : A ⟶ B)
    (M : PresheafOfModules.{u} B.obj) :
    (PresheafOfModules.sheafification (𝟙 A.obj)).obj
      ((PresheafOfModules.restrictScalars φ.hom).obj M) ⟶
    (restrictScalars φ).obj ((PresheafOfModules.sheafification (𝟙 B.obj)).obj M) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 A.obj)).symm
    ((PresheafOfModules.restrictScalars φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app M))

private theorem restrictSheafifyHom_toSheaf {A B : Sheaf J RingCat.{u}} (φ : A ⟶ B)
    (M : PresheafOfModules.{u} B.obj) :
    (toSheaf A).map (restrictSheafifyHom φ M) =
      𝟙 ((PresheafOfModules.toPresheaf B.obj ⋙
        presheafToSheaf J AddCommGrpCat).obj M) := by
  unfold restrictSheafifyHom
  rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  apply ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  rfl

@[irreducible] private def restrictSheafifyIso {A B : Sheaf J RingCat.{u}} (φ : A ⟶ B)
    (M : PresheafOfModules.{u} B.obj) :
    (PresheafOfModules.sheafification (𝟙 A.obj)).obj
      ((PresheafOfModules.restrictScalars φ.hom).obj M) ≅
    (restrictScalars φ).obj ((PresheafOfModules.sheafification (𝟙 B.obj)).obj M) := by
  have : IsIso (restrictSheafifyHom φ M) := by
    have : IsIso ((toSheaf A).map (restrictSheafifyHom φ M)) := by
      rw [restrictSheafifyHom_toSheaf]
      exact IsIso.id _
    exact isIso_of_reflects_iso _ (toSheaf A)
  exact asIso (restrictSheafifyHom φ M)

@[irreducible] private def scalarExtensionIso (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) :
    (restrictScalars (𝓻 φ)).obj (changeOfRings.{u, u, u} φ M) ≅ ∏ᶜ fun _ : Fin d ↦ M :=
  (restrictSheafifyIso (𝓻 φ) (changeOfRingsPresheaf.{u, u, u} φ M)).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (𝓡 R).obj)).mapIso
      (scalarExtensionPresheafIso φ d e M) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R).obj)).counit).app
      (∏ᶜ fun _ : Fin d ↦ M)

private theorem sheafify_unit_counit {A : Sheaf J RingCat.{u}}
    (N : PresheafOfModules.{u} A.obj) (M : SheafOfModules.{u} A)
    (f : N ⟶ M.val) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 A.obj)).unit.app N ≫
      ((PresheafOfModules.sheafification (𝟙 A.obj)).map f ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 A.obj)).counit.app M).val = f := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 A.obj)
  exact (adj.homEquiv N M).apply_symm_apply f

private theorem scalarExtensionIso_unit (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) :
    (PresheafOfModules.restrictScalars (𝓻 φ).hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.app
          (changeOfRingsPresheaf.{u, u, u} φ M)) ≫ (scalarExtensionIso φ d e M).hom.val =
      (scalarExtensionPresheafIso φ d e M).hom := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R).obj)
  have hunit : adj.unit.app ((PresheafOfModules.restrictScalars (𝓻 φ).hom).obj
      (changeOfRingsPresheaf.{u, u, u} φ M)) ≫ (restrictSheafifyHom (𝓻 φ)
        (changeOfRingsPresheaf.{u, u, u} φ M)).val =
      (PresheafOfModules.restrictScalars (𝓻 φ).hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.app
          (changeOfRingsPresheaf.{u, u, u} φ M)) := by
    change adj.homEquiv _ _ (restrictSheafifyHom (𝓻 φ)
      (changeOfRingsPresheaf.{u, u, u} φ M)) = _
    unfold restrictSheafifyHom
    exact (PresheafOfModules.sheafificationHomEquiv (𝟙 (𝓡 R).obj)).apply_symm_apply _
  have hh : (restrictSheafifyIso (𝓻 φ)
      (changeOfRingsPresheaf.{u, u, u} φ M)).hom =
      restrictSheafifyHom (𝓻 φ) (changeOfRingsPresheaf.{u, u, u} φ M) := by
    unfold restrictSheafifyIso
    rfl
  have hi : (restrictSheafifyHom (𝓻 φ) (changeOfRingsPresheaf.{u, u, u} φ M)).val ≫
      (restrictSheafifyIso (𝓻 φ) (changeOfRingsPresheaf.{u, u, u} φ M)).inv.val = 𝟙 _ := by
    rw [← hh, ← comp_val, Iso.hom_inv_id]
    rfl
  have hη : (PresheafOfModules.restrictScalars (𝓻 φ).hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.app
          (changeOfRingsPresheaf.{u, u, u} φ M)) ≫
        (restrictSheafifyIso (𝓻 φ) (changeOfRingsPresheaf.{u, u, u} φ M)).inv.val =
      adj.unit.app ((PresheafOfModules.restrictScalars (𝓻 φ).hom).obj
        (changeOfRingsPresheaf.{u, u, u} φ M)) := by
    rw [← hunit, Category.assoc, hi]
    change _ ≫ 𝟙 _ = _
    exact Category.comp_id _
  have hc := sheafify_unit_counit
    ((PresheafOfModules.restrictScalars (𝓻 φ).hom).obj
      (changeOfRingsPresheaf.{u, u, u} φ M)) (∏ᶜ fun _ : Fin d ↦ M)
        (scalarExtensionPresheafIso φ d e M).hom
  unfold scalarExtensionIso
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, asIso_hom, comp_val]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f ↦ f ≫ _) hη).trans hc)

private theorem scalarExtensionIso_tmul (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) (V : Cᵒᵖ)
    (s : S.obj.obj V) (m : M.val.obj V) (i : Fin d) :
    ((scalarExtensionIso φ d e M).hom ≫ Pi.π (fun _ : Fin d ↦ M) i).val.app V
      ((toSheafify J (changeOfRingsPresheaf.{u, u, u} φ M).presheaf).app V
        (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)) =
      ((e.inv ≫ Pi.π (fun _ : Fin d ↦ unit (𝓡 R)) i).val.app V s) • m := by
  have h := congrArg (fun f ↦ f.app V
    (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)) (scalarExtensionIso_unit φ d e M)
  change (Pi.π (fun _ : Fin d ↦ M) i).val.app V
      ((scalarExtensionIso φ d e M).hom.val.app V _) = _
  change (Pi.π (fun _ : Fin d ↦ M) i).val.app V
      (((PresheafOfModules.restrictScalars (𝓻 φ).hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.app
          (changeOfRingsPresheaf.{u, u, u} φ M)) ≫
        (scalarExtensionIso φ d e M).hom.val).app V _) = _
  rw [h]
  unfold scalarExtensionPresheafIso
  exact scalarExtensionApp_tmul φ d e M V s m i

private def scalarChangeMap (φ : R ⟶ S) {M N : SheafOfModules.{u} (𝓡 R)}
    (f : M ⟶ N) : changeOfRingsPresheaf.{u, u, u} φ M ⟶
      changeOfRingsPresheaf.{u, u, u} φ N where
  app V := (ModuleCat.extendScalars (φ.hom.app V).hom).map (f.val.app V)
  naturality := changeOfRingsHom_naturality φ M f

private theorem scalarPresheaf_naturality (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    {M N : SheafOfModules.{u} (𝓡 R)} (f : M ⟶ N) :
    (PresheafOfModules.restrictScalars (𝓻 φ).hom).map (scalarChangeMap φ f) ≫
      (scalarExtensionPresheafIso φ d e N).hom =
        (scalarExtensionPresheafIso φ d e M).hom ≫ (Limits.Pi.map (fun _ : Fin d ↦ f)).val := by
  ext V x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s m =>
    apply sectionProduct_ext d N V
    intro i
    change (Pi.π (fun _ : Fin d ↦ N) i).val.app V
      ((scalarExtensionPresheafIso φ d e N).hom.app V
        ((scalarChangeMap φ f).app V (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m))) = _
    have ht : (scalarChangeMap φ f).app V
        (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m) =
        s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] f.val.app V m := by
      exact ModuleCat.ExtendScalars.map_tmul _ _ _ _
    have hp := congrArg (fun g ↦ g.val.app V
      ((scalarExtensionApp φ d e M V).hom (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)))
      (Pi.map_π (fun _ : Fin d ↦ f) i)
    have hN := scalarExtensionApp_tmul φ d e N V s (f.val.app V m) i
    have hM := scalarExtensionApp_tmul φ d e M V s m i
    have hT := congrArg ((Pi.π (fun _ : Fin d ↦ N) i).val.app V ∘
      (scalarExtensionApp φ d e N V).hom) ht
    unfold scalarExtensionPresheafIso
    exact hT.trans (hN.trans (((f.val.app V).hom.map_smul _ _).symm.trans
      ((congrArg (f.val.app V) hM).symm.trans hp.symm)))

private theorem scalarExtension_hom_ext (φ : R ⟶ S)
    (M : SheafOfModules.{u} (𝓡 R)) (N : SheafOfModules.{u} (𝓡 R))
    (f g : (restrictScalars (𝓻 φ)).obj (changeOfRings.{u, u, u} φ M) ⟶ N)
    (h : (PresheafOfModules.restrictScalars (𝓻 φ).hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.app
          (changeOfRingsPresheaf.{u, u, u} φ M)) ≫ f.val =
      (PresheafOfModules.restrictScalars (𝓻 φ).hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.app
          (changeOfRingsPresheaf.{u, u, u} φ M)) ≫ g.val) : f = g := by
  let A := (PresheafOfModules.restrictScalars (𝓻 φ).hom).obj
    (changeOfRingsPresheaf.{u, u, u} φ M)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R).obj)
  let r := restrictSheafifyIso (𝓻 φ) (changeOfRingsPresheaf.{u, u, u} φ M)
  have hr : adj.unit.app A ≫ r.hom.val =
      (PresheafOfModules.restrictScalars (𝓻 φ).hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.app
          (changeOfRingsPresheaf.{u, u, u} φ M)) := by
    have hh : r.hom = restrictSheafifyHom (𝓻 φ)
        (changeOfRingsPresheaf.{u, u, u} φ M) := by
      dsimp only [r]
      unfold restrictSheafifyIso
      rfl
    rw [hh]
    change adj.homEquiv _ _ (restrictSheafifyHom (𝓻 φ)
      (changeOfRingsPresheaf.{u, u, u} φ M)) = _
    unfold restrictSheafifyHom
    exact (PresheafOfModules.sheafificationHomEquiv (𝟙 (𝓡 R).obj)).apply_symm_apply _
  apply (cancel_epi r.hom).mp
  apply (adj.homEquiv A N).injective
  change adj.unit.app A ≫ (r.hom ≫ f).val = adj.unit.app A ≫ (r.hom ≫ g).val
  simp only [comp_val, ← Category.assoc]
  rw [hr]
  exact h

private theorem scalarExtensionIso_naturality (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    {M N : SheafOfModules.{u} (𝓡 R)} (f : M ⟶ N) :
    (restrictScalars (𝓻 φ)).map (changeOfRingsHom φ M f) ≫
      (scalarExtensionIso φ d e N).hom =
        (scalarExtensionIso φ d e M).hom ≫ Limits.Pi.map (fun _ : Fin d ↦ f) := by
  apply scalarExtension_hom_ext φ M (∏ᶜ fun _ : Fin d ↦ N)
  let V := PresheafOfModules.restrictScalars (𝓻 φ).hom
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)
  have hη := congrArg V.map (adj.unit.naturality (scalarChangeMap φ f))
  simp only [Functor.map_comp] at hη
  change V.map (scalarChangeMap φ f) ≫ V.map (adj.unit.app _) =
      V.map (adj.unit.app _) ≫
        ((restrictScalars (𝓻 φ)).map (changeOfRingsHom φ M f)).val at hη
  let ηM := V.map (adj.unit.app (changeOfRingsPresheaf.{u, u, u} φ M))
  let ηN := V.map (adj.unit.app (changeOfRingsPresheaf.{u, u, u} φ N))
  let cM := (scalarExtensionIso φ d e M).hom.val
  let cN := (scalarExtensionIso φ d e N).hom.val
  let v := ((restrictScalars (𝓻 φ)).map (changeOfRingsHom φ M f)).val
  let q := (Limits.Pi.map (fun _ : Fin d ↦ f)).val
  change ηM ≫ (v ≫ cN) = ηM ≫ (cM ≫ q)
  calc
    ηM ≫ (v ≫ cN) = (ηM ≫ v) ≫ cN := (Category.assoc _ _ _).symm
    _ = (V.map (scalarChangeMap φ f) ≫ ηN) ≫ cN :=
      congrArg (fun t ↦ t ≫ cN) hη.symm
    _ = V.map (scalarChangeMap φ f) ≫ (ηN ≫ cN) := Category.assoc _ _ _
    _ = V.map (scalarChangeMap φ f) ≫ (scalarExtensionPresheafIso φ d e N).hom :=
      congrArg (fun t ↦ V.map (scalarChangeMap φ f) ≫ t)
        (scalarExtensionIso_unit φ d e N)
    _ = (scalarExtensionPresheafIso φ d e M).hom ≫ q :=
      scalarPresheaf_naturality φ d e f
    _ = (ηM ≫ cM) ≫ q :=
      congrArg (fun t ↦ t ≫ q) (scalarExtensionIso_unit φ d e M).symm
    _ = ηM ≫ (cM ≫ q) := Category.assoc _ _ _



@[irreducible] private def scalarComplexIso (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (P : CochainComplex (SheafOfModules.{u} (𝓡 R)) ℤ) :
    ((restrictScalars (𝓻 φ)).mapHomologicalComplex (.up ℤ)).obj
      (changeOfRingsComplex.{u, u} φ P) ≅ ∏ᶜ fun _ : Fin d ↦ P :=
  (HomologicalComplex.Hom.isoOfComponents
    (C₁ := ((restrictScalars (𝓻 φ)).mapHomologicalComplex (.up ℤ)).obj
      (changeOfRingsComplex.{u, u} φ P))
    (C₂ := ((finitePowerFunctor d).mapHomologicalComplex (.up ℤ)).obj P)
    (fun k ↦ scalarExtensionIso φ d e (P.X k)) (by
      intro k l h
      exact (scalarExtensionIso_naturality φ d e (P.d k l)).symm)) ≪≫
    finitePowerComplexIso d P

private theorem scalarComplexIso_projection (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (P : CochainComplex (SheafOfModules.{u} (𝓡 R)) ℤ) (i : Fin d) (k : ℤ) :
    ((scalarComplexIso φ d e P).hom ≫ Pi.π (fun _ : Fin d ↦ P) i).f k =
      (scalarExtensionIso φ d e (P.X k)).hom ≫
        Pi.π (fun _ : Fin d ↦ P.X k) i := by
  unfold scalarComplexIso
  simp only [Iso.trans_hom, Category.assoc, HomologicalComplex.comp_f]
  have h := finitePowerComplexIso_projection d P i k
  simp only [HomologicalComplex.comp_f] at h
  exact congrArg (_ ≫ ·) h

/-- A chosen finite basis gives the scalar-extension isomorphism of complexes,
normalized on elementary tensor sections.

Source: Stacks Project, Modules on Sites, Tags 03CY and 03EK; explicit basis
calculation in Bhatt--Scholze, Lemma 3.4.12.
(blueprint: lem-pur-finite-free-scalar-extension).

Proof: evaluate the basis isomorphism at every site object. Tensor its inverse
with the module and distribute over the finite product using the linear equivalence
`M ⊗ (Fin d → R) ≃ (Fin d → M)`. Its ith coordinate is `lambda_i(s) • m`.
Restriction compatibility follows from naturality of the basis coordinates and
semilinearity of module restrictions. Sheafify the resulting presheaf isomorphism;
restriction of scalars has the same underlying abelian sheafification, and the
sheafification counit identifies the sheafified finite product with itself.
The sheafification unit gives the displayed formula. Naturality in module maps
makes these degreewise isomorphisms commute with every differential. Finally,
the degreewise finite product complex is the categorical finite product of
complexes. The construction includes the empty product, where every module is zero. -/
theorem finiteFreeScalarExtension (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (P : CochainComplex (SheafOfModules.{u} (𝓡 R)) ℤ) :
    ∃ α : ((restrictScalars (𝓻 φ)).mapHomologicalComplex (.up ℤ)).obj
        (changeOfRingsComplex.{u, u} φ P) ≅ ∏ᶜ fun _ : Fin d ↦ P,
      ∀ (k : ℤ) (V : Cᵒᵖ) (s : S.obj.obj V) (p : (P.X k).val.obj V) (i : Fin d),
        (((α.hom ≫ Pi.π (fun _ : Fin d ↦ P) i).f k).val.app V)
          ((toSheafify J (changeOfRingsPresheaf.{u, u, u} φ (P.X k)).presheaf).app V
            (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] p)) =
          ((e.inv ≫ Pi.π (fun _ : Fin d ↦ unit (𝓡 R)) i).val.app V s) • p := by
  refine ⟨scalarComplexIso φ d e P, ?_⟩
  intro k V s p i
  rw [scalarComplexIso_projection]
  exact scalarExtensionIso_tmul φ d e (P.X k) V s p i

end SheafOfModules
