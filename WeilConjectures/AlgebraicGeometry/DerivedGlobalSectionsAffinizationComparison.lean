/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.GlobalSectionsDirectImageKInjectiveAcyclic

/-! # Derived global sections after affinization

## References

* Stacks Project, Cohomology, Tags 0D5T, 079V
-/

@[expose] public section

universe u wX wY wA
open CategoryTheory Opposite
namespace AlgebraicGeometry

private noncomputable def underived_comparison (X : Scheme.{u}) :
    RingedSpace.moduleDirectImage X.toSpecΓ.toLRSHom.toShHom ⋙
      (RingedSpace.globalSectionsFunctor (Spec Γ(X, ⊤)).toRingedSpace ⋙
        ModuleCat.restrictScalars (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom) ≅
      RingedSpace.globalSectionsFunctor X.toRingedSpace := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · change (ModuleCat.restrictScalars (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom).obj
      ((ModuleCat.restrictScalars X.toSpecΓ.appTop.hom).obj (M.val.obj (op ⊤))) ≅
      M.val.obj (op ⊤)
    exact (ModuleCat.restrictScalarsComp _ _).symm.app _ ≪≫
      (ModuleCat.restrictScalarsId' _ (by
        rw [← CommRingCat.hom_comp, Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
        rfl)).app _
  · intro M N f
    apply ModuleCat.hom_ext
    rfl

/-- Derived global sections factors through derived pushforward to the spectrum of
its own coefficient ring (Stacks, Tags 0D5T, 079V). -/
theorem derivedGlobalSections_affinization_comparison (X : Scheme.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))]
    [HasDerivedCategory.{wA}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))] :
    letI : HasDerivedCategory.{wA} (ModuleCat.{u} Γ(X, ⊤)) :=
      inferInstanceAs (HasDerivedCategory.{wA}
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))))
    Nonempty ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor ≅
      schemeDerivedDirectImage X.toSpecΓ ⋙
        (RingedSpace.globalSectionsFunctor (Spec Γ(X, ⊤)).toRingedSpace ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom).rightDerivedFunctor) := by
  let : HasDerivedCategory.{wA} (ModuleCat.{u} Γ(X, ⊤)) :=
    inferInstanceAs (HasDerivedCategory.{wA}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))))
  have : (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive :=
    RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let F := RingedSpace.moduleDirectImage X.toSpecΓ.toLRSHom.toShHom
  let G := RingedSpace.globalSectionsFunctor (Spec Γ(X, ⊤)).toRingedSpace ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom
  let β := Functor.rightDerivedFunctorCompUnit F G
  have hβ : (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor).IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      ((F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso _ (fun J ↦ ?_)
    obtain ⟨I, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective J
    change IsIso (β.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))
    have h₁ : IsIso (F.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := inferInstance
    have h₂ : IsIso (G.rightDerivedFunctorUnit.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) :=
      isIso_globalSections_restrictScalars_unit_on_directImage_kInjective
        X.toSpecΓ (Scheme.ΓSpecIso Γ(X, ⊤)).inv I
    dsimp only [β, Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  let e := Functor.rightDerivedUnique (F ⋙ G).rightDerivedFunctor
    (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
    (F ⋙ G).rightDerivedFunctorUnit β
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
  exact ⟨(Functor.rightDerivedFunctorNatIso (underived_comparison X)).symm ≪≫ e⟩

end AlgebraicGeometry
