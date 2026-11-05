/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Pi.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Finite-basis tensor evaluation

Source: Stacks Project, Modules on Sites, Tags 03EK, 03CY, 03DA and 03DB;
finite-basis consequence with explicit section formulas.
(blueprint: lem-pur-based-sheaf-tensor-evaluation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] CategoryTheory.Limits.limit

universe u vC uC
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  {R S : Sheaf J CommRingCat.{u}}

attribute [local irreducible] basedTensorProductSections changeOfRingsMap

@[irreducible] private def coordinateEquiv {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {d : ℕ}
    (q : (ModuleCat.restrictScalars φ).obj (ModuleCat.of B B) ≃ₗ[A] (Fin d → A))
    (M : ModuleCat.{u} A) :
    (ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj M) ≃ₗ[A]
      (Fin d → M) := by
  letI : Module A B := Module.compHom B φ
  exact TensorProduct.comm A B M ≪≫ₗ q.lTensor M ≪≫ₗ
    TensorProduct.piScalarRight A A M (Fin d)

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
set_option hygiene false in
local notation "𝓻" φ => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ

@[irreducible] private def basisCoordinates (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S))) (U : Cᵒᵖ) :
    (ModuleCat.restrictScalars (φ.hom.app U).hom).obj
      (ModuleCat.of (S.obj.obj U) (S.obj.obj U)) ≃ₗ[R.obj.obj U] (Fin d → R.obj.obj U) :=
  ((evaluation (𝓡 R) U).mapIso e.symm ≪≫
    basedTensorProductSections d (unit (𝓡 R)) U).toLinearEquiv

@[irreducible] private def tensorCoordinateApp (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) (V : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars (𝓻 φ).hom).obj
      (changeOfRingsPresheaf.{vC, uC, u} φ M)).obj V ≅ (∏ᶜ fun _ : Fin d ↦ M).val.obj V :=
  (coordinateEquiv (φ.hom.app V).hom (basisCoordinates φ d e V)
    (M.val.obj V)).toModuleIso ≪≫ (basedTensorProductSections (R := R) d M V).symm

@[irreducible] private def tensorCoordinates (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) :
    (PresheafOfModules.restrictScalars (𝓻 φ).hom).obj (changeOfRingsPresheaf.{vC, uC, u} φ M) ≅
      (∏ᶜ fun _ : Fin d ↦ M).val :=
  PresheafOfModules.isoMk (tensorCoordinateApp φ d e M) (by
    intro V W f
    ext x
    induction x using TensorProduct.induction_on with
    | zero => exact map_zero _ |>.trans (map_zero _).symm
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
        (map_add _ x y).symm)
    | tmul s m =>
      apply sectionProduct_ext d M W
      intro i
      change (Pi.π (fun _ : Fin d ↦ M) i).val.app W
          ((tensorCoordinateApp φ d e M W).hom (changeOfRingsMap φ M f
            (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m))) =
        (Pi.π (fun _ : Fin d ↦ M) i).val.app W
          ((∏ᶜ fun _ : Fin d ↦ M).val.map f
            ((tensorCoordinateApp φ d e M V).hom
              (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)))
      have ht := congrArg ((Pi.π (fun _ : Fin d ↦ M) i).val.app W ∘
        (tensorCoordinateApp φ d e M W).hom) (changeMap_tmul φ M f s m)
      exact ht.trans ((tensorCoordinateApp_tmul φ d e M W _ _ i).trans (by
        have hπ := PresheafOfModules.naturality_apply
          (Pi.π (fun _ : Fin d ↦ M) i).val f
          ((tensorCoordinateApp φ d e M V).hom
            (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m))
        have hc := tensorCoordinateApp_tmul φ d e M V s m i
        have hl := PresheafOfModules.map_smul M.val f
          (((e.inv ≫ Pi.π (fun _ : Fin d ↦ unit (𝓡 R)) i).val.app V) s) m
        have hb := PresheafOfModules.naturality_apply
          (e.inv ≫ Pi.π (fun _ : Fin d ↦ unit (𝓡 R)) i).val f s
        exact (congrArg (fun r ↦ r • M.val.map f m) hb).trans
          (hl.symm.trans ((congrArg (M.val.map f) hc).symm.trans hπ.symm)))))

@[irreducible] private def tensorSheafCoordinates (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S)))
    (F : SheafOfModules.{u} (𝓡 R)) :
    (restrictScalars.{u} (𝓻 φ)).obj ((tensorFunctor φ).obj F) ≅
      ∏ᶜ fun _ : Fin d ↦ F := by
  have := tensorUnit_isIso φ d e F
  let Q := PresheafOfModules.restrictScalars (𝓻 φ).hom
  let η := Q.mapIso (asIso (tensorUnit φ F))
  let β := tensorCoordinates φ d e F
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

@[irreducible] private def tensorCoordinateIso (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S))) :
    tensorFunctor φ ⋙ restrictScalars.{u} (𝓻 φ) ≅
      Functor.pi' (fun _ : Fin d ↦ 𝟭 (SheafOfModules.{u} (𝓡 R))) ⋙ Pi.functor (Fin d) :=
  NatIso.ofComponents (tensorSheafCoordinates φ d e) (by
    intro F G f
    apply SheafOfModules.hom_ext
    have := tensorUnit_isIso φ d e F
    let Q := PresheafOfModules.restrictScalars (𝓻 φ).hom
    apply (cancel_epi (Q.map (tensorUnit φ F))).1
    change Q.map (tensorUnit φ F) ≫
        (Q.map ((tensorFunctor φ).map f).val ≫
          (tensorSheafCoordinates φ d e G).hom.val) =
      Q.map (tensorUnit φ F) ≫
        ((tensorSheafCoordinates φ d e F).hom.val ≫
          (Limits.Pi.map (fun _ : Fin d ↦ f)).val)
    calc
      _ = (Q.map (tensorUnit φ F) ≫ Q.map ((tensorFunctor φ).map f).val) ≫
          (tensorSheafCoordinates φ d e G).hom.val := (Category.assoc _ _ _).symm
      _ = (Q.map ((tensorPresheafFunctor φ).map f) ≫ Q.map (tensorUnit φ G)) ≫
          (tensorSheafCoordinates φ d e G).hom.val := by
        have hn := congrArg Q.map (tensorUnit_naturality φ f).symm
        simp only [Functor.map_comp] at hn
        exact congrArg (fun k ↦ k ≫ (tensorSheafCoordinates φ d e G).hom.val) hn
      _ = Q.map ((tensorPresheafFunctor φ).map f) ≫
          (tensorCoordinates φ d e G).hom := by
        exact (Category.assoc _ _ _).trans
          (congrArg (fun k ↦ Q.map ((tensorPresheafFunctor φ).map f) ≫ k)
            (tensorSheafCoordinates_unit φ d e G))
      _ = (tensorCoordinates φ d e F).hom ≫
          (Limits.Pi.map (fun _ : Fin d ↦ f)).val :=
        tensorCoordinates_naturality φ d e f
      _ = _ := ((congrArg (fun k ↦ k ≫ (Limits.Pi.map (fun _ : Fin d ↦ f)).val)
        (tensorSheafCoordinates_unit φ d e F)).symm).trans (Category.assoc _ _ _))

-- The long conjunction repeatedly elaborates sectionwise products and scalar restrictions.
end SheafOfModules
