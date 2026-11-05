/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCoefficientLayerData
public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerTensorComplex
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientLocalHomologyModels
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Complete.CompleteCoefficientDatumSupplement
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # The actual coefficient kernel as a constant residue module

Source: Stacks Project, sites-cohomology.tex, Tag 094I.
(blueprint: lem-weil-pbc-finite-quotient-layer-kernel-constant-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local irreducible] HasDerivedCategory.standard completedAdicChangeData

namespace FiniteLayerKernelProof

attribute [local instance] constantUnitInjective constantUnitSurjective

@[irreducible] private def restrictionCompIso (X : Scheme.{t})
    {R S T : Sheaf (ProEt.topology X) RingCat.{t + 1}}
    (α : R ⟶ S) (β : S ⟶ T) :
    SheafOfModules.restrictScalars.{t + 1} (α ≫ β) ≅
      SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α :=
  NatIso.ofComponents (fun N ↦
    { hom.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).hom
      hom.val.naturality i := by ext m; rfl
      inv.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).inv
      inv.val.naturality i := by ext m; rfl }) (by intro M N f; ext U x; rfl)

@[irreducible] private def restrictionIdIso (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) :
    SheafOfModules.restrictScalars.{t + 1} (𝟙 R) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun N ↦
    { hom.val.app U := (ModuleCat.restrictScalarsId'App _ rfl (N.val.obj U)).hom
      hom.val.naturality i := by ext m; rfl
      inv.val.app U := (ModuleCat.restrictScalarsId'App _ rfl (N.val.obj U)).inv
      inv.val.naturality i := by ext m; rfl }) (by intro M N f; ext U x; rfl)

@[irreducible] private def constantRestrictionIso (X : Scheme.{t})
    {B D : Type t} [CommRing B] [CommRing D] (f : B →+* D) (M : ModuleCat.{t} D) :
    (baseConstantFunctor X B).obj ((ModuleCat.restrictScalars f).obj M) ≅
      (SheafOfModules.restrictScalars (adicModuleMap X f)).obj
        ((baseConstantFunctor X D).obj M) := by
  let α := koszulConstantUnit X B
  let β := koszulConstantUnit X D
  let φ := adicModuleMap X f
  have : Presheaf.IsLocallyInjective (ProEt.topology X) α :=
    (koszulConstantUnit_local X B).1
  have : Presheaf.IsLocallySurjective (ProEt.topology X) α :=
    (koszulConstantUnit_local X B).2
  have : Presheaf.IsLocallyInjective (ProEt.topology X) β :=
    (koszulConstantUnit_local X D).1
  have : Presheaf.IsLocallySurjective (ProEt.topology X) β :=
    (koszulConstantUnit_local X D).2
  let L := ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
  let L' := ModuleCat.uliftFunctor.{t + 1, t} D ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} D ≃+* D).toRingHom
  let P := (siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} B)).obj
    (L.obj ((ModuleCat.restrictScalars f).obj M))
  let P' := (siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} D)).obj
    (L'.obj M)
  let N := (baseConstantFunctor X D).obj M
  let a := (PresheafOfModules.sheafificationAdjunction β).unit.app P'
  let c : CommRingCat.of (ULift.{t + 1} B) ⟶ CommRingCat.of (ULift.{t + 1} D) :=
    CommRingCat.ofHom
                  (show ULift.{t + 1} B →+* ULift.{t + 1} D from RingHom.ulift f)
  let g : P ⟶ (PresheafOfModules.restrictScalars α).obj
      ((SheafOfModules.restrictScalars φ).obj N).val :=
    { app := fun U ↦ ModuleCat.ofHom (X := P.obj U)
        (Y := ((PresheafOfModules.restrictScalars α).obj
          ((SheafOfModules.restrictScalars φ).obj N).val).obj U)
        { toFun := a.app U
          map_add' := (a.app U).hom.map_add
          map_smul' := fun b m ↦ by
            have hs : β.app U ((RingHom.ulift f) b) = φ.hom.app U (α.app U b) :=
              ConcreteCategory.congr_hom
                (NatTrans.congr_app (toSheafify_naturality (ProEt.topology X)
                  ((Functor.const X.ProEtᵒᵖ).map c)) U) b
            change a.app U ((RingHom.ulift f) b • (show P'.obj U from m)) =
              φ.hom.app U (α.app U b) • (show N.val.obj U from a.app U m)
            rw [← hs]
            exact (a.app U).hom.map_smul ((RingHom.ulift f) b) m }
      naturality := fun {U V} h ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        exact congrArg (fun k ↦ k m) (a.naturality h) }
  let e : (baseConstantFunctor X B).obj ((ModuleCat.restrictScalars f).obj M) ⟶
      (SheafOfModules.restrictScalars φ).obj N :=
    (PresheafOfModules.sheafificationHomEquiv α).symm g
  have hfac : toSheafify (ProEt.topology X) P.presheaf ≫
      ((SheafOfModules.toSheaf _).map e).hom =
        (PresheafOfModules.toPresheaf _).map g := by
    exact congrArg ((PresheafOfModules.toPresheaf _).map)
      ((PresheafOfModules.sheafificationHomEquiv α (P := P)
        (F := (SheafOfModules.restrictScalars φ).obj N)).apply_symm_apply g)
  have : Presheaf.IsLocallyInjective (ProEt.topology X)
      ((PresheafOfModules.toPresheaf _).map g) :=
    inferInstanceAs (Presheaf.IsLocallyInjective (ProEt.topology X)
      (toSheafify (ProEt.topology X) P.presheaf))
  have : Presheaf.IsLocallySurjective (ProEt.topology X)
      ((PresheafOfModules.toPresheaf _).map g) :=
    inferInstanceAs (Presheaf.IsLocallySurjective (ProEt.topology X)
      (toSheafify (ProEt.topology X) P.presheaf))
  have : Presheaf.IsLocallyInjective (ProEt.topology X)
      ((SheafOfModules.toSheaf _).map e).hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      (ProEt.topology X) _ hfac
  have : Presheaf.IsLocallySurjective (ProEt.topology X)
      ((SheafOfModules.toSheaf _).map e).hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac (ProEt.topology X) hfac
  have : IsIso ((SheafOfModules.toSheaf _).map e) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨inferInstance, inferInstance⟩
  have : IsIso e := isIso_of_reflects_iso e (SheafOfModules.toSheaf _)
  exact asIso e

@[irreducible] private def changeUnitIso (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S) [IsIso φ] :
    𝟭 _ ≅ completedAdicChange X φ ⋙ SheafOfModules.restrictScalars.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ) := by
  have := changeIsEquivalence X φ
  let a := (completedAdjunction X φ).choose
  exact asIso a.unit

section CoefficientMap
variable (X : Scheme.{t}) {B D : Type t} [CommRing B] [CommRing D]
  {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
  (φB : adicConstantRing X B ⟶ R) (φD : adicConstantRing X D ⟶ S)
  (f : B →+* D) (ψ : R ⟶ S)
  (hsq : adicConstantMap X f ≫ φD = φB ≫ ψ)

@[irreducible] private def coefficientPresheafHom : coefficientPresheaf X f ⟶
    (PresheafOfModules.restrictScalars (koszulConstantUnit X B)).obj
      (coefficientModule X φB ψ).val where
  app U := ModuleCat.ofHom (X := (coefficientPresheaf X f).obj U)
    (Y := ((PresheafOfModules.restrictScalars (koszulConstantUnit X B)).obj
      (coefficientModule X φB ψ).val).obj U)
    { toFun := fun x ↦ φD.hom.app U ((koszulConstantUnit X D).app U x)
      map_add' := fun x y ↦ by rw [map_add, map_add]
      map_smul' := fun b x ↦ by
        have hunit : (koszulConstantUnit X D).app U ((RingHom.ulift f) b) =
            (adicConstantMap X f).hom.app U ((koszulConstantUnit X B).app U b) :=
          ConcreteCategory.congr_hom
            (NatTrans.congr_app (toSheafify_naturality (ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).map
                (CommRingCat.ofHom
                  (show ULift.{t + 1} B →+* ULift.{t + 1} D from RingHom.ulift f)))) U) b
        have hscalar := ConcreteCategory.congr_hom
          (NatTrans.congr_app (congrArg (fun a ↦ a.hom) hsq) U)
            ((koszulConstantUnit X B).app U b)
        change φD.hom.app U ((koszulConstantUnit X D).app U
          ((RingHom.ulift f) b * (show ULift.{t + 1} D from x))) = _
        rw [map_mul, map_mul, hunit]
        exact congrArg (fun z ↦ z * φD.hom.app U ((koszulConstantUnit X D).app U x))
          hscalar }
  naturality {U V} a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom
      ((koszulConstantUnit X D ≫ ((forgetCommRing X).map φD).hom).naturality a) x

@[irreducible] private def coefficientHom :
    (baseConstantFunctor X B).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of D D)) ⟶
      coefficientModule X φB ψ :=
  (PresheafOfModules.sheafificationHomEquiv (koszulConstantUnit X B)).symm
    (coefficientPresheafHom X φB φD f ψ hsq)

end CoefficientMap

@[irreducible] private def coefficientRestrictionIso (X : Scheme.{t})
    {B D : Type t} [CommRing B] [CommRing D]
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φB : adicConstantRing X B ⟶ R) (φD : adicConstantRing X D ⟶ S)
    [IsIso φB] [IsIso φD] (f : B →+* D) (ψ : R ⟶ S)
    (h : adicConstantMap X f ≫ φD = φB ≫ ψ) (M : ModuleCat.{t} D) :
    (SheafOfModules.restrictScalars.{t + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map ψ)).obj
        ((finiteCoefficientConstantFunctor X D φD).obj M) ≅
      (finiteCoefficientConstantFunctor X B φB).obj ((ModuleCat.restrictScalars f).obj M) := by
  let H := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})
  let G := SheafOfModules.restrictScalars.{t + 1} (H.map φB)
  have : G.IsEquivalence := restrictionIsEquivalence X (H.mapIso (asIso φB))
  have hh : H.map φB ≫ H.map ψ = adicModuleMap X f ≫ H.map φD := by
    change H.map φB ≫ H.map ψ = H.map (adicConstantMap X f) ≫ H.map φD
    rw [← H.map_comp, ← H.map_comp, h]
  apply G.preimageIso
  exact ((restrictionCompIso X (H.map φB) (H.map ψ)).app _).symm ≪≫
    (eqToIso (congrArg (SheafOfModules.restrictScalars.{t + 1}) hh)).app _ ≪≫
    (restrictionCompIso X (adicModuleMap X f) (H.map φD)).app _ ≪≫
    (SheafOfModules.restrictScalars (adicModuleMap X f)).mapIso
      (((changeUnitIso X φD).app ((baseConstantFunctor X D).obj M)).symm) ≪≫
    (constantRestrictionIso X f M).symm ≪≫
    (changeUnitIso X φB).app
      ((baseConstantFunctor X B).obj ((ModuleCat.restrictScalars f).obj M))

end FiniteLayerKernelProof

end AlgebraicGeometry.Scheme
