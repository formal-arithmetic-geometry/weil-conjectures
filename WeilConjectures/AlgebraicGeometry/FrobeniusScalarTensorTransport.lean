/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleTensorScalarExtensionDefinitionsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.FrobeniusIntegralDiscreteTransportInvertible
import all WeilConjectures.AlgebraicGeometry.ProEtaleIsomorphismInverseImage
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # Invertibility of semilinear scalar tensor transport

Source: Stacks Project, Modules on Sites, Tags 03EK and 03EL.
(blueprint: new-weil-frobenius-scalar-tensor-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped ChangeOfRings TensorProduct
namespace WeilConjectures

private instance (priority := 3000) rootSiteSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _

attribute [local implicit_reducible] sheafCompose Functor.sheafPushforwardContinuous
  MorphismProperty.Over.pullback Scheme.instCategoryProEt
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'
  SheafOfModules.changeOfRingsOfUniverses ModuleCat.extendScalars ModuleCat.ExtendScalars.obj'
  SheafOfModules.toSheaf PresheafOfModules.sheafification PresheafOfModules.sheafify
  SheafOfModules.changeOfRingsPresheafOfUniverses PresheafOfModules.presheaf

section TensorTransport

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
  {R' S' : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
  (α : R ⟶ S) (α' : R' ⟶ S')
  (ρ : R ⟶ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj R')
  (σ : S ⟶ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj S')
  (h : α ≫ σ = ρ ≫ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map α')
  (M : SheafOfModules.{u + 1}
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
  (N : SheafOfModules.{u + 1}
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R'))
  (β : (SheafOfModules.toSheaf _).obj M ⟶
    (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).obj
      ((SheafOfModules.toSheaf _).obj N))
  (hb : ∀ (U : Y.ProEtᵒᵖ) (a : R.obj.obj U) (x : M.val.obj U),
    β.hom.app U (a • x) =
      (show R'.obj.obj ((proEtaleBaseChange g).op.obj U) from ρ.hom.app U a) •
        (show N.val.obj ((proEtaleBaseChange g).op.obj U) from β.hom.app U x))

private abbrev transportRawY :=
  SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α M

private abbrev transportRawX :=
  SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} α' N

include h hb in
private def transportRawApp (U : Y.ProEtᵒᵖ) :
    (transportRawY α M).presheaf.obj U ⟶
      (transportRawX α' N).presheaf.obj ((proEtaleBaseChange g).op.obj U) := by
  let V := (proEtaleBaseChange g).op.obj U
  let : Module (R.obj.obj U) (S.obj.obj U) := Module.compHom _ (α.hom.app U).hom
  let : Module (R'.obj.obj V) (S'.obj.obj V) := Module.compHom _ (α'.hom.app V).hom
  let ρU : R.obj.obj U →+* R'.obj.obj V := (ρ.hom.app U).hom
  let σU : S.obj.obj U →+* S'.obj.obj V := (σ.hom.app U).hom
  let fS : S.obj.obj U →ₛₗ[ρU] S'.obj.obj V :=
    { toFun := σU
      map_add' := map_add σU
      map_smul' := by
        intro a b
        have he : σU (α.hom.app U a) = α'.hom.app V (ρU a) :=
          congrArg (fun k ↦ k.hom.app U a) h
        change σU (α.hom.app U a * b) = α'.hom.app V (ρU a) * σU b
        rw [map_mul, he] }
  let fM : M.val.obj U →ₛₗ[ρU] N.val.obj V :=
    { toFun := β.hom.app U
      map_add' := map_add _
      map_smul' := hb U }
  exact AddCommGrpCat.ofHom (TensorProduct.map fS fM).toAddMonoidHom

include h hb in
private theorem transportRawApp_tmul (U : Y.ProEtᵒᵖ)
    (b : S.obj.obj U) (x : M.val.obj U) :
    transportRawApp g α α' ρ σ h M N β hb U (b ⊗ₜ[_, (α.hom.app U).hom] x) =
      (show S'.obj.obj ((proEtaleBaseChange g).op.obj U) from σ.hom.app U b)
        ⊗ₜ[_, (α'.hom.app ((proEtaleBaseChange g).op.obj U)).hom]
        (show N.val.obj ((proEtaleBaseChange g).op.obj U) from β.hom.app U x) := by
  rfl

attribute [local irreducible] transportRawApp

include h hb in
private def transportRaw :
    (transportRawY α M).presheaf ⟶
      (proEtaleBaseChange g).op ⋙ (transportRawX α' N).presheaf where
  app := transportRawApp g α α' ρ σ h M N β hb
  naturality := by
    intro U V i
    ext z
    change transportRawApp g α α' ρ σ h M N β hb V
        ((transportRawY α M).presheaf.map i z) =
      (transportRawX α' N).presheaf.map ((proEtaleBaseChange g).op.map i)
        (transportRawApp g α α' ρ σ h M N β hb U z)
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul b x =>
      change transportRawApp g α α' ρ σ h M N β hb V
          (SheafOfModules.changeOfRingsMapOfUniverses α M i (b ⊗ₜ[_, _] x)) =
        SheafOfModules.changeOfRingsMapOfUniverses α' N ((proEtaleBaseChange g).op.map i)
          (transportRawApp g α α' ρ σ h M N β hb U (b ⊗ₜ[_, _] x))
      have hY := SheafOfModules.changeOfRingsMap_tmulOfUniverses α M i b x
      have hX := SheafOfModules.changeOfRingsMap_tmulOfUniverses α' N
        ((proEtaleBaseChange g).op.map i)
        (show S'.obj.obj ((proEtaleBaseChange g).op.obj U) from σ.hom.app U b)
        (show N.val.obj ((proEtaleBaseChange g).op.obj U) from β.hom.app U x)
      refine (congrArg (transportRawApp g α α' ρ σ h M N β hb V) hY).trans ?_
      refine (transportRawApp_tmul g α α' ρ σ h M N β hb V _ _).trans ?_
      refine Eq.trans ?_ ((congrArg
        (SheafOfModules.changeOfRingsMapOfUniverses α' N ((proEtaleBaseChange g).op.map i))
        (transportRawApp_tmul g α α' ρ σ h M N β hb U b x)).trans hX).symm
      apply congrArg₂ (fun
        (b : S'.obj.obj ((proEtaleBaseChange g).op.obj V))
        (x : N.val.obj ((proEtaleBaseChange g).op.obj V)) ↦ b ⊗ₜ[_, _] x)
      · exact ConcreteCategory.congr_hom (σ.hom.naturality i) b
      · exact ConcreteCategory.congr_hom (β.hom.naturality i) x

include h hb in
private theorem transportRawApp_isIso [IsIso ρ] [IsIso σ] [IsIso β]
    (U : Y.ProEtᵒᵖ) :
    IsIso (transportRawApp g α α' ρ σ h M N β hb U) := by
  let V := (proEtaleBaseChange g).op.obj U
  let : Module (R.obj.obj U) (S.obj.obj U) := Module.compHom _ (α.hom.app U).hom
  let : Module (R'.obj.obj V) (S'.obj.obj V) := Module.compHom _ (α'.hom.app V).hom
  unfold transportRawApp
  apply (ConcreteCategory.isIso_iff_bijective _).2
  apply tensorMap_bijective
  · exact ConcreteCategory.bijective_of_isIso (ρ.hom.app U)
  · exact ConcreteCategory.bijective_of_isIso (σ.hom.app U)
  · exact ConcreteCategory.bijective_of_isIso (β.hom.app U)

end TensorTransport

/-- Scalar extension preserves an invertible semilinear transport along a scheme isomorphism.
Source: Stacks Project, Modules on Sites, sheafification and tensor pullback (Tags 03EK, 03EL).
Proof: the two semilinear factors induce a bijective tensor map on every object,
by tensoring their semilinear equivalences over the scalar-ring isomorphism.
Naturality follows on pure tensors and hence on all tensors by additive induction.
The displayed formula identifies the sheafification unit followed by φ with this
raw tensor isomorphism followed by the pulled-back sheafification unit. The site
base-change equivalence is cocontinuous, so the latter unit remains locally
bijective. Two-out-of-three for sheafification equivalences makes φ invertible.
Zero section rings and the empty scheme need no exception.
(blueprint: new-weil-frobenius-scalar-tensor-transport). -/
theorem frobeniusScalarTensorTransport_isIso
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {R' S' : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (α : R ⟶ S) (α' : R' ⟶ S')
    (ρ : R ⟶ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj R')
    (σ : S ⟶ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj S')
    (h : α ≫ σ = ρ ≫ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map α')
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (N : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R'))
    (β : (SheafOfModules.toSheaf _).obj M ⟶
      (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf _).obj N))
    (hb : ∀ (U : Y.ProEtᵒᵖ) (a : R.obj.obj U) (x : M.val.obj U),
      β.hom.app U (a • x) =
        (show R'.obj.obj ((proEtaleBaseChange g).op.obj U) from ρ.hom.app U a) •
          (show N.val.obj ((proEtaleBaseChange g).op.obj U) from β.hom.app U x))
    [IsIso g]
    (hρ : IsIso ρ) (hσ : IsIso σ) (hβ : IsIso β)
    (φ : (SheafOfModules.toSheaf ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)).obj
        (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α M) ⟶
      (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S')).obj
          (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α' N)))
    (hform : ∀ (U : Y.ProEtᵒᵖ) (b : S.obj.obj U) (x : M.val.obj U),
      φ.hom.app U (SheafOfModules.scalarExtensionSection α M U b x) =
        SheafOfModules.scalarExtensionSection α' N ((proEtaleBaseChange g).op.obj U)
          (σ.hom.app U b) (β.hom.app U x)) : IsIso φ := by
  have := hρ
  have := hσ
  have := hβ
  have : IsIso (transportRaw g α α' ρ σ h M N β hb) :=
    (NatTrans.isIso_iff_isIso_app _).2
      (fun U ↦ transportRawApp_isIso g α α' ρ σ h M N β hb U)
  let ηY : (transportRawY α M).presheaf ⟶
      ((SheafOfModules.toSheaf ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)).obj
        (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α M)).obj :=
    toSheafify (ProEt.topology Y) (transportRawY α M).presheaf
  let ηX : (proEtaleBaseChange g).op ⋙ (transportRawX α' N).presheaf ⟶
      ((proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S')).obj
          (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α' N))).obj :=
    Functor.whiskerLeft (proEtaleBaseChange g).op
      (toSheafify (ProEt.topology X) (transportRawX α' N).presheaf)
  have hη : (ProEt.topology Y).W ηX := by
    let e := AlgebraicGeometry.Scheme.isoBaseChangeEquivalence g
    have : e.inverse.IsContinuous (ProEt.topology X) (ProEt.topology Y) := by
      change (proEtaleIsoPostcompose g).IsContinuous _ _
      exact AlgebraicGeometry.Scheme.isoPostcompose_continuous g
    let : (proEtaleBaseChange g).IsCocontinuous (ProEt.topology Y) (ProEt.topology X) :=
      (e.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
        (CoverPreserving.of_isContinuous e.inverse _ _)
    have : Presheaf.IsLocallyInjective (ProEt.topology Y) ηX :=
      Presheaf.isLocallyInjective_whisker (ProEt.topology Y) (ProEt.topology X)
      (proEtaleBaseChange g)
      (toSheafify (ProEt.topology X) (transportRawX α' N).presheaf)
    have : Presheaf.IsLocallySurjective (ProEt.topology Y) ηX :=
      Presheaf.isLocallySurjective_whisker (ProEt.topology Y) (ProEt.topology X)
      (proEtaleBaseChange g)
      (toSheafify (ProEt.topology X) (transportRawX α' N).presheaf)
    exact (ProEt.topology Y).W_of_isLocallyBijective ηX
  have heq : ηY ≫ φ.hom = transportRaw g α α' ρ σ h M N β hb ≫ ηX := by
    ext U z
    change φ.hom.app U (ηY.app U z) =
      ηX.app U (transportRawApp g α α' ρ σ h M N β hb U z)
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul b x =>
      change φ.hom.app U (SheafOfModules.scalarExtensionSection α M U b x) =
        (toSheafify (ProEt.topology X) (transportRawX α' N).presheaf).app
          ((proEtaleBaseChange g).op.obj U)
          (transportRawApp g α α' ρ σ h M N β hb U (b ⊗ₜ[_, _] x))
      rw [transportRawApp_tmul]
      exact hform U b x
  apply ((ProEt.topology Y).W_sheafToPresheaf_map_iff_isIso φ).mp
  apply (ProEt.topology Y).W.of_precomp ηY φ.hom
    ((ProEt.topology Y).W_toSheafify (transportRawY α M).presheaf)
  rw [heq]
  exact (ProEt.topology Y).W.comp_mem _ _
    (((ProEt.topology Y).W_iff _).2 inferInstance) hη


end WeilConjectures
