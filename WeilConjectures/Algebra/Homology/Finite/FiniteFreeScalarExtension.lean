/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.Algebra.Homology.ChangeOfRingsComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.Finite.FinitePowerComplex
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Basis coordinates for finite free extension of sheaves

Source: Stacks Project, Modules on Sites, Tags 03CY and 03EK;
Bhatt--Scholze, Lemma 3.4.12.
(blueprint: lem-pur-finite-free-scalar-extension).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] CategoryTheory.Limits.limit

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace SheafOfModules
section General
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]
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
      (changeOfRingsPresheaf.{v, u, u} φ M)).obj V ≅ (∏ᶜ fun _ : Fin d ↦ M).val.obj V := by
  let A := R.obj.obj V
  let B := S.obj.obj V
  let ρ := (φ.hom.app V).hom
  let : Algebra A B := ρ.toAlgebra
  exact (TensorProduct.congr (sectionBasis φ d e V) (LinearEquiv.refl A (M.val.obj V)) ≪≫ₗ
    TensorProduct.comm A (Fin d → A) (M.val.obj V) ≪≫ₗ
    TensorProduct.piScalarRight A A (M.val.obj V) (Fin d)).toModuleIso ≪≫
      (sectionProductIso d M V).symm

attribute [local irreducible] changeOfRingsMap

@[irreducible] private def scalarExtensionPresheafIso (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) :
    (PresheafOfModules.restrictScalars (𝓻 φ).hom).obj (changeOfRingsPresheaf.{v, u, u} φ M) ≅
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

section SheafComparison
attribute [local irreducible] changeOfRingsPresheaf

@[irreducible] private def tensorUnit (φ : R ⟶ S) (M : SheafOfModules.{u} (𝓡 R)) :
    changeOfRingsPresheaf.{v, u, u} φ M ⟶ (changeOfRings.{v, u, u} φ M).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.app
    (changeOfRingsPresheaf.{v, u, u} φ M)

@[irreducible] private def scalarExtensionIso (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) :
    (restrictScalars (𝓻 φ)).obj (changeOfRings.{v, u, u} φ M) ≅ ∏ᶜ fun _ : Fin d ↦ M := by
  have := tensorUnit_isIso φ d e M
  let Q := PresheafOfModules.restrictScalars (𝓻 φ).hom
  let η := Q.mapIso (asIso (tensorUnit φ M))
  let β := scalarExtensionPresheafIso φ d e M
  exact
    { hom := ⟨η.inv ≫ β.hom⟩
      inv := ⟨β.inv ≫ η.hom⟩
      hom_inv_id := by
        apply SheafOfModules.hom_ext
        change (η.inv ≫ β.hom) ≫ (β.inv ≫ η.hom) = 𝟙 _
        simp
      inv_hom_id := by
        apply SheafOfModules.hom_ext
        change (β.inv ≫ η.hom) ≫ (η.inv ≫ β.hom) = 𝟙 _
        simp }

end SheafComparison

end General

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R S : Sheaf J CommRingCat.{u}}
set_option hygiene false in
local notation "𝓡" T => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T
set_option hygiene false in
local notation "𝓻" φ => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ

@[irreducible] private def restrictSheafifyHom {A B : Sheaf J RingCat.{u}} (φ : A ⟶ B)
    (M : PresheafOfModules.{u} B.obj) :
    (PresheafOfModules.sheafification (𝟙 A.obj)).obj
      ((PresheafOfModules.restrictScalars φ.hom).obj M) ⟶
    (restrictScalars φ).obj ((PresheafOfModules.sheafification (𝟙 B.obj)).obj M) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 A.obj)).symm
    ((PresheafOfModules.restrictScalars φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app M))

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

end SheafOfModules
