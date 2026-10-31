/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
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

/-- Evaluate a finite power using its coordinate projections.
Source: Stacks 03DB, sectionwise limits
(blueprint: lem-pur-based-sheaf-tensor-evaluation). -/
def basedTensorProductSections (d : ℕ)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (U : Cᵒᵖ) :
    (∏ᶜ fun _ : Fin d ↦ M).val.obj U ≅
      ModuleCat.of (R.obj.obj U) (Fin d → M.val.obj U) :=
  PreservesProduct.iso
    (evaluation.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U)
      (fun _ : Fin d ↦ M) ≪≫ ModuleCat.piIsoPi (fun _ : Fin d ↦ M.val.obj U)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
private theorem sections_coordinate (d : ℕ)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (U : Cᵒᵖ) (x : (∏ᶜ fun _ : Fin d ↦ M).val.obj U) (i : Fin d) :
    (basedTensorProductSections d M U).hom x i = (Pi.π (fun _ : Fin d ↦ M) i).val.app U x := by
  let E := evaluation ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U
  let f := fun _ : Fin d ↦ M
  let q : ModuleCat.of (R.obj.obj U) (Fin d → M.val.obj U) ⟶ M.val.obj U :=
    ModuleCat.ofHom (LinearMap.proj i)
  have h : (basedTensorProductSections d M U).hom ≫ q = (Pi.π f i).val.app U := by
    unfold basedTensorProductSections
    exact (Category.assoc (PreservesProduct.iso E f).hom
      (ModuleCat.piIsoPi (fun _ : Fin d ↦ M.val.obj U)).hom q).trans
      ((congrArg (fun g ↦ (PreservesProduct.iso E f).hom ≫ g)
        (ModuleCat.piIsoPi_hom_ker_subtype (fun _ : Fin d ↦ M.val.obj U) i)).trans
        (piComparison_comp_π E f i))
  exact congrArg (fun g ↦ g x) h

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
private theorem sectionProduct_ext (d : ℕ)
    (M : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : Cᵒᵖ) (x y : (∏ᶜ fun _ : Fin d ↦ M).val.obj V)
    (h : ∀ i : Fin d, (Pi.π (fun _ : Fin d ↦ M) i).val.app V x =
      (Pi.π (fun _ : Fin d ↦ M) i).val.app V y) : x = y := by
  apply (basedTensorProductSections (R := R) d M V).toLinearEquiv.injective
  funext i
  exact (sections_coordinate (R := R) d M V x i).trans
    ((h i).trans (sections_coordinate (R := R) d M V y i).symm)

private theorem changeMap_tmul (φ : R ⟶ S)
    (M : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {V W : Cᵒᵖ} (f : V ⟶ W) (s : S.obj.obj V) (m : M.val.obj V) :
    changeOfRingsMap φ M f (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m) =
      S.obj.map f s ⊗ₜ[R.obj.obj W, (φ.hom.app W).hom] M.val.map f m :=
  Classical.choose_spec (exists_changeOfRingsMap φ M f) s m

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

private theorem coordinateEquiv_tmul {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {d : ℕ}
    (q : (ModuleCat.restrictScalars φ).obj (ModuleCat.of B B) ≃ₗ[A] (Fin d → A))
    (M : ModuleCat.{u} A) (a : B) (x : M) (i : Fin d) :
    coordinateEquiv φ q M (a ⊗ₜ[A, φ] x) i = q a i • x := by
  let : Module A B := Module.compHom B φ
  unfold coordinateEquiv
  change (TensorProduct.piScalarRight A A M (Fin d))
    (q.lTensor M ((TensorProduct.comm A B M) (a ⊗ₜ[A] x))) i = _
  change (TensorProduct.piScalarRightHom A A M (Fin d)) (x ⊗ₜ[A] q a) i = _
  exact congrArg (fun z ↦ z i) (TensorProduct.piScalarRightHom_tmul A A M (Fin d) x (q a))

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

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
private theorem basisCoordinates_apply (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S)))
    (U : Cᵒᵖ) (a : S.obj.obj U) (i : Fin d) :
    basisCoordinates φ d e U a i =
      (e.inv ≫ Pi.π (fun _ : Fin d ↦ unit (𝓡 R)) i).val.app U a := by
  unfold basisCoordinates
  exact sections_coordinate d (unit (𝓡 R)) U (e.inv.val.app U a) i

@[irreducible] private def tensorCoordinateApp (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) (V : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars (𝓻 φ).hom).obj
      (changeOfRingsPresheaf.{vC, uC, u} φ M)).obj V ≅ (∏ᶜ fun _ : Fin d ↦ M).val.obj V :=
  (coordinateEquiv (φ.hom.app V).hom (basisCoordinates φ d e V)
    (M.val.obj V)).toModuleIso ≪≫ (basedTensorProductSections (R := R) d M V).symm

private theorem tensorCoordinateApp_tmul (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 φ)).obj (unit (𝓡 S)))
    (M : SheafOfModules.{u} (𝓡 R)) (V : Cᵒᵖ)
    (s : S.obj.obj V) (m : M.val.obj V) (i : Fin d) :
    (Pi.π (fun _ : Fin d ↦ M) i).val.app V
      ((tensorCoordinateApp φ d e M V).hom (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)) =
      ((e.inv ≫ Pi.π (fun _ : Fin d ↦ unit (𝓡 R)) i).val.app V s) • m := by
  have hp := sections_coordinate (R := R) d M V
    ((tensorCoordinateApp φ d e M V).hom
      (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)) i
  refine hp.symm.trans ?_
  unfold tensorCoordinateApp
  change (basedTensorProductSections (R := R) d M V).hom
    ((basedTensorProductSections (R := R) d M V).inv
      (coordinateEquiv (φ.hom.app V).hom (basisCoordinates φ d e V)
        (M.val.obj V) (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m))) i = _
  exact (congrArg (fun z ↦ z i)
    ((basedTensorProductSections (R := R) d M V).inv_hom_id_apply _)).trans
    ((coordinateEquiv_tmul (φ.hom.app V).hom (basisCoordinates φ d e V)
      (M.val.obj V) s m i).trans
        (congrArg (fun r ↦ r • m) (basisCoordinates_apply φ d e V s i)))

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


private theorem tensor_isSheaf (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S)))
    (F : SheafOfModules.{u} (𝓡 R)) :
    Presheaf.IsSheaf J (changeOfRingsPresheaf.{vC, uC, u} φ F).presheaf := by
  change Presheaf.IsSheaf J
    ((PresheafOfModules.restrictScalars (𝓻 φ).hom).obj
      (changeOfRingsPresheaf.{vC, uC, u} φ F)).presheaf
  exact (Presheaf.isSheaf_of_iso_iff
    ((PresheafOfModules.toPresheaf (𝓡 R).obj).mapIso (tensorCoordinates φ d e F))).2
      (∏ᶜ fun _ : Fin d ↦ F).isSheaf

private def tensorPresheafFunctor (φ : R ⟶ S) :
    SheafOfModules.{u} (𝓡 R) ⥤ PresheafOfModules.{u} (𝓡 S).obj where
  obj F := changeOfRingsPresheaf.{vC, uC, u} φ F
  map {F G} f :=
    { app := fun U ↦ (ModuleCat.extendScalars (φ.hom.app U).hom).map (f.val.app U)
      naturality := changeOfRingsHom_naturality φ F f }
  map_id F := by
    ext U : 1
    exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_id _
  map_comp f g := by
    ext U : 1
    exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_comp _ _

private def tensorFunctor (φ : R ⟶ S) :
    SheafOfModules.{u} (𝓡 R) ⥤ SheafOfModules.{u} (𝓡 S) :=
  tensorPresheafFunctor φ ⋙ PresheafOfModules.sheafification (𝟙 (𝓡 S).obj)

private theorem tensorFunctor_additive (φ : R ⟶ S) : (tensorFunctor φ).Additive := by
  have : (tensorPresheafFunctor φ).Additive := by
    constructor
    intro F G f g
    ext U : 1
    have : (ModuleCat.extendScalars (φ.hom.app U).hom).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).left_adjoint_additive
    exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_add
  have : (PresheafOfModules.sheafification.{u} (𝟙 (𝓡 S).obj)).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact inferInstanceAs
    (tensorPresheafFunctor φ ⋙ PresheafOfModules.sheafification (𝟙 (𝓡 S).obj)).Additive

private def tensorUnit (φ : R ⟶ S) (F : SheafOfModules.{u} (𝓡 R)) :
    changeOfRingsPresheaf.{vC, uC, u} φ F ⟶ (changeOfRings.{vC, uC, u} φ F).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.app
    (changeOfRingsPresheaf.{vC, uC, u} φ F)

private theorem tensorUnit_isIso (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S)))
    (F : SheafOfModules.{u} (𝓡 R)) : IsIso (tensorUnit φ F) := by
  have := isIso_toSheafify J (tensor_isSheaf φ d e F)
  have : IsIso ((PresheafOfModules.toPresheaf (𝓡 S).obj).map (tensorUnit φ F)) :=
    inferInstanceAs (IsIso (toSheafify J (changeOfRingsPresheaf.{vC, uC, u} φ F).presheaf))
  exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf (𝓡 S).obj)

private theorem tensorUnit_naturality (φ : R ⟶ S)
    {F G : SheafOfModules.{u} (𝓡 R)} (f : F ⟶ G) :
    (tensorPresheafFunctor φ).map f ≫ tensorUnit φ G =
      tensorUnit φ F ≫ ((tensorFunctor φ).map f).val := by
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.naturality
    ((tensorPresheafFunctor φ).map f)

private theorem tensorCoordinates_naturality (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S)))
    {F G : SheafOfModules.{u} (𝓡 R)} (f : F ⟶ G) :
    (PresheafOfModules.restrictScalars (𝓻 φ).hom).map
        ((tensorPresheafFunctor φ).map f) ≫ (tensorCoordinates φ d e G).hom =
      (tensorCoordinates φ d e F).hom ≫ (Limits.Pi.map (fun _ : Fin d ↦ f)).val := by
  ext V x
  induction x using TensorProduct.induction_on with
  | zero => exact map_zero _ |>.trans (map_zero _).symm
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
      (map_add _ x y).symm)
  | tmul s m =>
    apply sectionProduct_ext d G V
    intro i
    change (Pi.π (fun _ : Fin d ↦ G) i).val.app V
      ((tensorCoordinates φ d e G).hom.app V
        (((tensorPresheafFunctor φ).map f).app V (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m))) = _
    have ht : ((tensorPresheafFunctor φ).map f).app V
        (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m) =
        s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] f.val.app V m := by
      exact ModuleCat.ExtendScalars.map_tmul _ _ _ _
    have hp := congrArg (fun g ↦ g.val.app V
      ((tensorCoordinateApp φ d e F V).hom (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)))
      (Pi.map_π (fun _ : Fin d ↦ f) i)
    have hN := tensorCoordinateApp_tmul φ d e G V s (f.val.app V m) i
    have hM := tensorCoordinateApp_tmul φ d e F V s m i
    have hT := congrArg ((Pi.π (fun _ : Fin d ↦ G) i).val.app V ∘
      (tensorCoordinateApp φ d e G V).hom) ht
    unfold tensorCoordinates
    exact hT.trans (hN.trans (((f.val.app V).hom.map_smul _ _).symm.trans
      ((congrArg (f.val.app V) hM).symm.trans hp.symm)))

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

private theorem tensorSheafCoordinates_unit (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S)))
    (F : SheafOfModules.{u} (𝓡 R)) :
    (PresheafOfModules.restrictScalars (𝓻 φ).hom).map (tensorUnit φ F) ≫
      (tensorSheafCoordinates φ d e F).hom.val = (tensorCoordinates φ d e F).hom := by
  have := tensorUnit_isIso φ d e F
  let Q := PresheafOfModules.restrictScalars (𝓻 φ).hom
  let η := Q.mapIso (asIso (tensorUnit φ F))
  unfold tensorSheafCoordinates
  change η.hom ≫ (η.inv ≫ (tensorCoordinates φ d e F).hom) = _
  exact η.hom_inv_id_assoc _

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

private theorem power_exact (D : Type*) [Category D] [Abelian D] (d : ℕ) :
    PreservesFiniteLimits
        (Functor.pi' (fun _ : Fin d ↦ 𝟭 D) ⋙ Pi.functor (Fin d)) ∧
      PreservesFiniteColimits
        (Functor.pi' (fun _ : Fin d ↦ 𝟭 D) ⋙ Pi.functor (Fin d)) := by
  let : HasFiniteBiproducts D := Abelian.hasFiniteBiproducts
  let T := Functor.pi' (fun _ : Fin d ↦ 𝟭 D) ⋙ Pi.functor (Fin d)
  let L := Functor.const (Discrete (Fin d)) ⋙ lim (J := Discrete (Fin d)) (C := D)
  let Q := Functor.const (Discrete (Fin d)) ⋙ colim (J := Discrete (Fin d)) (C := D)
  let e : L ≅ T := NatIso.ofComponents
    (fun M ↦ (Pi.isoLimit ((Functor.const (Discrete (Fin d))).obj M)).symm) (by
    intro X Y f
    apply Pi.hom_ext
    intro i
    simp only [Category.assoc]
    change limMap ((Functor.const (Discrete (Fin d))).map f) ≫
        (Pi.isoLimit ((Functor.const (Discrete (Fin d))).obj Y)).inv ≫ Pi.π _ i =
      (Pi.isoLimit ((Functor.const (Discrete (Fin d))).obj X)).inv ≫
        Limits.Pi.map (fun _ : Fin d ↦ f) ≫ Pi.π _ i
    rw [Pi.isoLimit_inv_π, Pi.map_π, ← Category.assoc, Pi.isoLimit_inv_π, limMap_π]
    rfl)
  have : PreservesFiniteLimits L := inferInstance
  have : PreservesFiniteColimits Q := inferInstance
  let e' : Q ≅ T := Functor.isoWhiskerLeft _
    (HasBiproductsOfShape.colimIsoLim (J := Fin d) (C := D)) ≪≫ e
  exact ⟨preservesFiniteLimits_of_natIso e, preservesFiniteColimits_of_natIso e'⟩

private theorem coordinateEquiv_symm {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {d : ℕ}
    (q : (ModuleCat.restrictScalars φ).obj (ModuleCat.of B B) ≃ₗ[A] (Fin d → A))
    (M : ModuleCat.{u} A) (x : Fin d → M) :
    (coordinateEquiv φ q M).symm x =
      ∑ i : Fin d, q.symm (Pi.single i 1) ⊗ₜ[A, φ] x i := by
  let : Module A B := Module.compHom B φ
  have hx : x = ∑ i : Fin d, Pi.single i (x i) := by
    ext i
    simp
  conv_lhs => rw [hx, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold coordinateEquiv
  simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    TensorProduct.piScalarRight_symm_single]
  rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
private theorem basisCoordinates_symm (one : C) (hOne : IsTerminal one)
    (φ : R ⟶ S) (d : ℕ) (b : Fin d → S.obj.obj (op one))
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S)))
    (he : ∀ (U : Cᵒᵖ) (r : Fin d → R.obj.obj U),
      e.hom.val.app U ((basedTensorProductSections d (unit (𝓡 R)) U).inv r) =
        ∑ i : Fin d, φ.hom.app U (r i) * S.obj.map (hOne.from U.unop).op (b i))
    (U : Cᵒᵖ) (i : Fin d) :
    (basisCoordinates φ d e U).symm (Pi.single i 1) =
      S.obj.map (hOne.from U.unop).op (b i) := by
  unfold basisCoordinates
  change e.hom.val.app U
    ((basedTensorProductSections d (unit (𝓡 R)) U).inv (Pi.single i (1 : R.obj.obj U))) = _
  rw [he]
  simp [Pi.single_apply]

private theorem tensorCoordinateApp_inv (one : C) (hOne : IsTerminal one)
    (φ : R ⟶ S) (d : ℕ) (b : Fin d → S.obj.obj (op one))
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars.{u} (𝓻 φ)).obj (unit (𝓡 S)))
    (he : ∀ (U : Cᵒᵖ) (r : Fin d → R.obj.obj U),
      e.hom.val.app U ((basedTensorProductSections d (unit (𝓡 R)) U).inv r) =
        ∑ i : Fin d, φ.hom.app U (r i) * S.obj.map (hOne.from U.unop).op (b i))
    (F : SheafOfModules.{u} (𝓡 R)) (U : Cᵒᵖ)
    (x : (∏ᶜ fun _ : Fin d ↦ F).val.obj U) :
    (tensorCoordinateApp φ d e F U).inv x =
      ∑ i : Fin d, S.obj.map (hOne.from U.unop).op (b i)
        ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom]
          ((Pi.π (fun _ : Fin d ↦ F) i).val.app U x) := by
  unfold tensorCoordinateApp
  change (coordinateEquiv (φ.hom.app U).hom (basisCoordinates φ d e U)
    (F.val.obj U)).symm ((basedTensorProductSections d F U).hom x) = _
  refine (coordinateEquiv_symm (φ.hom.app U).hom (basisCoordinates φ d e U)
    (F.val.obj U) ((basedTensorProductSections d F U).hom x)).trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg₂ (fun a z ↦ a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] z)
    (basisCoordinates_symm one hOne φ d b e he U i) (sections_coordinate d F U x i)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
private theorem restriction_limits (α : R ⟶ S) :
    PreservesFiniteLimits (restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α)) := by
  let A := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let B := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S
  have : PreservesFiniteLimits (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α) ⋙ toSheaf A) :=
    inferInstanceAs (PreservesFiniteLimits (toSheaf.{u} B))
  have : ReflectsFiniteLimits (toSheaf.{u} A) :=
    reflectsFiniteLimits_of_reflectsIsomorphisms (toSheaf.{u} A)
  exact preservesFiniteLimits_of_reflects_of_preserves _ (toSheaf A)

private theorem restriction_colimits (α : R ⟶ S) :
    PreservesFiniteColimits (restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α)) := by
  let A := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let B := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S
  have : PreservesFiniteColimits (toSheaf.{u} A) := inferInstance
  have : ReflectsFiniteColimits (toSheaf.{u} A) :=
    reflectsFiniteColimitsOfReflectsIsomorphisms (toSheaf.{u} A)
  have : PreservesFiniteColimits (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α) ⋙ toSheaf A) :=
    inferInstanceAs (PreservesFiniteColimits (toSheaf.{u} B))
  exact preservesFiniteColimits_of_reflects_of_preserves _ (toSheaf A)

private theorem comp_zero_of_image_eq_kernel {D : Type*} [Category D] [Abelian D]
    {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : imageSubobject f = kernelSubobject g) : f ≫ g = 0 := by
  have hz : (imageSubobject f).arrow ≫ g = 0 := by
    rw [← Subobject.ofLE_arrow h.le, Category.assoc, kernelSubobject_arrow_comp, comp_zero]
  rw [← imageSubobject_arrow_comp f, Category.assoc, hz, comp_zero]

private theorem exact_image_iff {D E : Type*} [Category D] [Category E]
    [Abelian D] [Abelian E] (T : D ⥤ E) [T.Additive] [T.Faithful]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    imageSubobject f = kernelSubobject g ↔
      imageSubobject (T.map f) = kernelSubobject (T.map g) := by
  constructor
  · intro h
    let K := ShortComplex.mk f g (comp_zero_of_image_eq_kernel f g h)
    exact (K.map T).exact_iff_image_eq_kernel.mp
      ((K.exact_iff_image_eq_kernel.mpr h).map T)
  · intro h
    have hfg : f ≫ g = 0 := T.map_injective (by
      rw [Functor.map_comp, comp_zero_of_image_eq_kernel (T.map f) (T.map g) h,
        Functor.map_zero])
    let K := ShortComplex.mk f g hfg
    exact K.exact_iff_image_eq_kernel.mp
      (T.reflects_exact_of_faithful K ((K.map T).exact_iff_image_eq_kernel.mpr h))

set_option linter.unusedVariables false in
set_option maxHeartbeats 200000 in
-- The long conjunction repeatedly elaborates sectionwise products and scalar restrictions.
set_option synthInstance.maxHeartbeats 80000 in
/-- The full finite-basis evaluation assertion, including exactness and complexes.
Source: Stacks 03EK, 03CY, 03DA, 03DB; algebra 00CX; homology 010N and 010V.
(blueprint: lem-pur-based-sheaf-tensor-evaluation).

Proof:
1. Sectionwise limits identify finite products with coordinate tuples. The basis
isomorphism e and its inverse give q_i(b_j)=delta_ij and sum_i phi(q_i(a))b_i=a.
This includes rank zero. These coordinates commute with restriction (03DB).
2. The balanced rule a tensor f maps to (q_i(a) f)_i induces the coordinate map
by the tensor universal property (00CX). Its inverse is sum_i b_i tensor f_i.
The two basis identities prove both inverse equations on tuples and pure tensors.
3. Restrictions commute with both formulas. Thus the tensor presheaf is isomorphic
to the finite power of F. Coordinatewise gluing proves it is a sheaf, even for
empty covering sieves (03EK).
4. The sheafification adjunction (03CY), applied over S with its identity map,
gives the inverse of the unit on this already sheaf tensor presheaf. Compose with
the coordinate maps to get Phi and its displayed inverse.
5. The unit is theta. In coordinates Phi theta is the coordinate map, hence the
identity between the two coordinate copies. Its inverse is the displayed finite
sum. Naturality in F and restriction hold on pure tensors, hence everywhere by
tensor generation. The pure-tensor characterization implies uniqueness and basis
independence (00CX, 03EK).
6. For arbitrary phi, restriction keeps the same abelian sheaves and maps.
The forgetful theorem lem-weil-pbc-module-sheaves-colimits-forgetful identifies
kernels sectionwise and cokernels by sheafification for both coefficient rings.
Their comparisons are isomorphisms; the inverse of a linear bijection is linear.
7. Restriction reflects kernel and cokernel universal properties by the same
inverse-linearity argument. Images and kernels are the same underlying abelian
subsheaves, so equality of image and kernel is preserved and reflected, even
without first assuming a zero composite. The kernel/cokernel finite-exactness
criterion lem-sfb-kernel-cokernel-finite-exactness gives finite exactness.
8. Finite powers are additive. Factor a map into a power of a kernel coordinatewise;
factor a map out of a power of a cokernel using the coordinate inclusions and sum.
Uniqueness is coordinatewise, including the empty family. The same criterion
makes this finite power exact in the abelian category of module sheaves.
9. Tensor maps are additive on pure tensors and after sheafification by uniqueness.
The coordinate natural isomorphism Res T = finite power, exactness of that power,
and reflection in Step 7 give preservation of kernels and cokernels by T.
Apply the finite-exactness criterion again.
10. The one-object identity site specializes this to ordinary modules A to B,
with sheafification the identity and no further hypothesis on the rings.
11. Apply theta in each degree. Both differential composites send a tensor to
its differential tensor the same scalar. Tensor generation gives the chain
identity. The inverses give the inverse chain map; naturality holds degreewise.
There is no boundedness or totalization assumption (010V).
-/
theorem basedSheafTensorEvaluation :
    (∀ (φ : R ⟶ S),
      PreservesFiniteLimits (restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)) ∧
      PreservesFiniteColimits (restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)) ∧
      ∀ (M N P : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
        (f : M ⟶ N) (g : N ⟶ P),
        (imageSubobject f = kernelSubobject g ↔
          imageSubobject ((restrictScalars.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).map f) =
          kernelSubobject ((restrictScalars.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).map g))) ∧
    (∀ (A B : Type u) [CommRing A] [CommRing B] (φ : A →+* B)
      (d : ℕ) (b : Module.Basis (Fin d) A
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))),
      (ModuleCat.extendScalars.{u, u, u} φ).Additive ∧
      PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} φ) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} φ)) ∧
    ∀ (one : C) (hOne : IsTerminal one) (φ : R ⟶ S) (d : ℕ)
      (b : Fin d → S.obj.obj (op one))
      (e : (∏ᶜ fun _ : Fin d ↦
          unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ≅
        (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
          (unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
      (he : ∀ (U : Cᵒᵖ) (r : Fin d → R.obj.obj U),
        e.hom.val.app U
          ((basedTensorProductSections d
            (unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) U).inv r) =
          ∑ i : Fin d, φ.hom.app U (r i) * S.obj.map (hOne.from U.unop).op (b i)),
      ∃ E : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
          SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S),
      ∃ hE : ∀ F : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R), E.obj F = changeOfRings
            φ F,
        (∀ {F G : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (f : F ⟶ G), E.map f =
          eqToHom (hE F) ≫ changeOfRingsHom.{vC, uC, u} φ F f ≫ eqToHom (hE G).symm) ∧
      ∃ (_ : E.Additive),
        PreservesFiniteLimits E ∧ PreservesFiniteColimits E ∧
      ∃ Φ : E ⋙ restrictScalars.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ) ≅
          Functor.pi' (fun _ : Fin d ↦ 𝟭 (SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ⋙
            Pi.functor (Fin d),
      ∃ θ : ∀ (F : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ),
          (changeOfRingsPresheaf.{vC, uC, u} φ F).obj U ≅ (E.obj F).val.obj U,
        (∀ F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R), Presheaf.IsSheaf J
            (changeOfRingsPresheaf.{vC, uC, u} φ F).presheaf) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ) (a :
            S.obj.obj U) (x : F.val.obj U),
          (θ F U).hom (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) =
            (eqToHom (hE F).symm).val.app U
              ((toSheafify J (changeOfRingsPresheaf.{vC, uC, u} φ F).presheaf).app U
                (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ) (a :
            S.obj.obj U) (x : F.val.obj U) (i : Fin d),
          (Pi.π (fun _ : Fin d ↦ F) i).val.app U
            ((Φ.hom.app F).val.app U
              ((θ F U).hom (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) =
            ((e.inv ≫ Pi.π
              (fun _ : Fin d ↦ unit
                ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) i).val.app U a) •
            x) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ) (x : (∏ᶜ fun
            _ : Fin d ↦ F).val.obj U),
          (Φ.inv.app F).val.app U x = (θ F U).hom
            (∑ i : Fin d, S.obj.map (hOne.from U.unop).op (b i)
              ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom]
                ((Pi.π (fun _ : Fin d ↦ F) i).val.app U x))) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ) (x : (E.obj
            F).val.obj U),
          (θ F U).inv x = ∑ i : Fin d,
            S.obj.map (hOne.from U.unop).op (b i) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom]
              ((Pi.π (fun _ : Fin d ↦ F) i).val.app U ((Φ.hom.app F).val.app U x))) ∧
        (∀ (F G : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (f : F ⟶ G) (U : Cᵒᵖ)
            (x : (changeOfRingsPresheaf.{vC, uC, u} φ F).obj U),
          (E.map f).val.app U ((θ F U).hom x) =
            (θ G U).hom ((ModuleCat.extendScalars.{u, u, u}
              (R := R.obj.obj U) (S := S.obj.obj U) (φ.hom.app U).hom).map
              (f.val.app U) x)) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U V : Cᵒᵖ) (j : U ⟶
            V) (x : (changeOfRingsPresheaf.{vC, uC, u} φ F).obj U),
          (E.obj F).val.map j ((θ F U).hom x) =
            (θ F V).hom ((changeOfRingsPresheaf.{vC, uC, u} φ F).map j x)) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ) (k :
            (changeOfRingsPresheaf.{vC, uC, u} φ F).obj U ⟶ (E.obj F).val.obj U),
          (∀ (a : S.obj.obj U) (x : F.val.obj U),
            k (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) =
              (θ F U).hom (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) →
            k = (θ F U).hom) ∧
        (∀ K : CochainComplex (SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ,
          ∀ U : Cᵒᵖ,
          ∃ α : (((evaluation.{u}
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U) ⋙
              ModuleCat.extendScalars.{u, u, u}
              (R := R.obj.obj U) (S := S.obj.obj U) (φ.hom.app U).hom).mapHomologicalComplex (.up
            ℤ)).obj K ≅
            (Functor.mapHomologicalComplex
              (evaluation.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S) U)
              (.up ℤ)).obj ((E.mapHomologicalComplex (.up ℤ)).obj K),
            ∀ j : ℤ, α.hom.f j = (θ (K.X j) U).hom ∧
              α.inv.f j = (θ (K.X j) U).inv) := by
  refine ⟨?_, ?_, ?_⟩
  · intro φ
    have := restriction_limits φ
    have := restriction_colimits φ
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro M N P f g
    let T := restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)
    have : (T ⋙ toSheaf _).Faithful :=
      inferInstanceAs (toSheaf.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)).Faithful
    have : T.Faithful := Functor.Faithful.of_comp T (toSheaf _)
    exact exact_image_iff T f g
  · intro A B _ _ φ d b
    let : Algebra A B := φ.toAlgebra
    have : Module.Free A B := Module.Free.of_basis b
    have hφ : φ.Flat := by
      change Module.Flat A B
      infer_instance
    have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
    refine ⟨?_, inferInstance, inferInstance⟩
    exact (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive
  · intro one hOne φ d b e he
    let E := tensorFunctor φ
    have : E.Additive := tensorFunctor_additive φ
    have hE (F : SheafOfModules.{u} (𝓡 R)) : E.obj F = changeOfRings φ F := rfl
    refine ⟨E, hE, ?_, tensorFunctor_additive φ, ?_, ?_, tensorCoordinateIso φ d e, ?_⟩
    · intro F G f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
    · have := restriction_limits φ
      have := restriction_colimits φ
      have : (restrictScalars.{u} (𝓻 φ)).ReflectsIsomorphisms := by
        have : (restrictScalars.{u} (𝓻 φ) ⋙ toSheaf (𝓡 R)).ReflectsIsomorphisms :=
          inferInstanceAs (toSheaf.{u} (𝓡 S)).ReflectsIsomorphisms
        exact reflectsIsomorphisms_of_comp _ (toSheaf (𝓡 R))
      have := (power_exact (SheafOfModules.{u} (𝓡 R)) d).1
      have : PreservesFiniteLimits (E ⋙ restrictScalars.{u} (𝓻 φ)) :=
        preservesFiniteLimits_of_natIso (tensorCoordinateIso φ d e).symm
      exact preservesFiniteLimits_of_reflects_of_preserves E (restrictScalars.{u} (𝓻 φ))
    · have := restriction_limits φ
      have := restriction_colimits φ
      have : (restrictScalars.{u} (𝓻 φ)).ReflectsIsomorphisms := by
        have : (restrictScalars.{u} (𝓻 φ) ⋙ toSheaf (𝓡 R)).ReflectsIsomorphisms :=
          inferInstanceAs (toSheaf.{u} (𝓡 S)).ReflectsIsomorphisms
        exact reflectsIsomorphisms_of_comp _ (toSheaf (𝓡 R))
      have := (power_exact (SheafOfModules.{u} (𝓡 R)) d).2
      have : PreservesFiniteColimits (E ⋙ restrictScalars.{u} (𝓻 φ)) :=
        preservesFiniteColimits_of_natIso (tensorCoordinateIso φ d e).symm
      exact preservesFiniteColimits_of_reflects_of_preserves E (restrictScalars.{u} (𝓻 φ))
    let hη (F : SheafOfModules.{u} (𝓡 R)) := tensorUnit_isIso φ d e F
    let θ (F : SheafOfModules.{u} (𝓡 R)) (U : Cᵒᵖ) :=
      (PresheafOfModules.evaluation (𝓡 S).obj U).mapIso (asIso (tensorUnit φ F))
    refine ⟨θ, tensor_isSheaf φ d e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro F U a x
      rfl
    · intro F U a x i
      simp only [tensorCoordinateIso, NatIso.ofComponents_hom_app]
      have hh := congrArg (fun f ↦ f.app U) (tensorSheafCoordinates_unit φ d e F)
      have hv := ConcreteCategory.congr_hom hh
        (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
      change (tensorSheafCoordinates φ d e F).hom.val.app U
        ((tensorUnit φ F).app U _) = _ at hv
      change (Pi.π (fun _ : Fin d ↦ F) i).val.app U
        ((tensorSheafCoordinates φ d e F).hom.val.app U
          ((tensorUnit φ F).app U _)) = _
      refine (congrArg ((Pi.π (fun _ : Fin d ↦ F) i).val.app U) hv).trans ?_
      unfold tensorCoordinates
      change (Pi.π (fun _ : Fin d ↦ F) i).val.app U
        ((tensorCoordinateApp φ d e F U).hom _) = _
      exact tensorCoordinateApp_tmul φ d e F U a x i
    · intro F U x
      simp only [tensorCoordinateIso, NatIso.ofComponents_inv_app]
      change (tensorSheafCoordinates φ d e F).inv.val.app U x = _
      unfold tensorSheafCoordinates tensorCoordinates
      change (tensorUnit φ F).app U ((tensorCoordinateApp φ d e F U).inv x) = _
      exact congrArg ((tensorUnit φ F).app U)
        (tensorCoordinateApp_inv one hOne φ d b e he F U x)
    · intro F U x
      simp only [tensorCoordinateIso, NatIso.ofComponents_hom_app]
      have h := congrArg (fun f ↦ f.app U)
        (tensorSheafCoordinates_unit φ d e F)
      have hh := ConcreteCategory.congr_hom h ((θ F U).inv x)
      unfold tensorCoordinates at hh
      change (tensorSheafCoordinates φ d e F).hom.val.app U
        ((θ F U).hom ((θ F U).inv x)) =
          (tensorCoordinateApp φ d e F U).hom ((θ F U).inv x) at hh
      have hh' : (tensorSheafCoordinates φ d e F).hom.val.app U x =
          (tensorCoordinateApp φ d e F U).hom ((θ F U).inv x) :=
        (congrArg ((tensorSheafCoordinates φ d e F).hom.val.app U)
          ((θ F U).inv_hom_id_apply x)).symm.trans hh
      exact ((tensorCoordinateApp φ d e F U).hom_inv_id_apply ((θ F U).inv x)).symm.trans
        ((congrArg (tensorCoordinateApp φ d e F U).inv hh'.symm).trans
          (tensorCoordinateApp_inv one hOne φ d b e he F U
            ((tensorSheafCoordinates φ d e F).hom.val.app U x)))
    · intro F G f U x
      exact (ConcreteCategory.congr_hom
        (congrArg (fun k ↦ k.app U) (tensorUnit_naturality φ f)) x).symm
    · intro F U V j x
      exact (PresheafOfModules.naturality_apply (tensorUnit φ F) j x).symm
    · intro F U k hk
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      exact hk 1 x
    · intro K U
      have : (ModuleCat.extendScalars (R := R.obj.obj U) (S := S.obj.obj U)
          (φ.hom.app U).hom).Additive :=
        (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).left_adjoint_additive
      let α := HomologicalComplex.Hom.isoOfComponents
        (C₁ := (((evaluation.{u} (𝓡 R) U) ⋙
          ModuleCat.extendScalars (R := R.obj.obj U) (S := S.obj.obj U)
            (φ.hom.app U).hom).mapHomologicalComplex (.up ℤ)).obj K)
        (C₂ := ((evaluation.{u} (𝓡 S) U).mapHomologicalComplex (.up ℤ)).obj
          ((E.mapHomologicalComplex (.up ℤ)).obj K))
        (fun j ↦ θ (K.X j) U) (by
          intro i j hij
          change (tensorUnit φ (K.X i)).app U ≫
            ((tensorFunctor φ).map (K.d i j)).val.app U =
              ((tensorPresheafFunctor φ).map (K.d i j)).app U ≫
                (tensorUnit φ (K.X j)).app U
          have h := tensorUnit_naturality (C := C) (J := J)
            (R := R) (S := S) φ (K.d i j)
          exact (congrArg (fun k : changeOfRingsPresheaf.{vC, uC, u} φ (K.X i) ⟶
            (changeOfRings.{vC, uC, u} φ (K.X j)).val ↦ k.app U) h).symm)
      exact ⟨α, fun j ↦ ⟨rfl, rfl⟩⟩


end SheafOfModules
