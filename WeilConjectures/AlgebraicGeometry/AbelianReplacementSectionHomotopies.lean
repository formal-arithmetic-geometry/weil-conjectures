/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Ext


public import WeilConjectures.AlgebraicGeometry.AbelianCounitResolutionCalculation
import WeilConjectures.AlgebraicGeometry.AbelianReplacementSectionHomotopiesCore
import WeilConjectures.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.SchemeModulesEnoughInjectives

/-! # Comparing module replacements with the abelian counit lift

## References

* Stacks Project, Tags 01FB, 013P, 013S and 03FD
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution

private theorem quasiIso_of_replacement_section_homotopy {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : X.Modules} (I : InjectiveResolution F)
    (K : CochainComplex Y.Modules ℕ)
    (hK : ∀ n : ℕ, Injective (K.X n))
    (l : ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K)
    (hl : QuasiIso l)
    (a : ((moduleSections X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ≅
      ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj
        (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex))
    (q : ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((abelianSections X).mapHomologicalComplex (.up ℕ)).obj
        (standardAbelianResolution X F).cocomplex)
    (hql : Nonempty (Homotopy
      ((a.hom ≫ ((moduleSections Y).mapHomologicalComplex (.up ℕ)).map l) ≫ q)
      (((abelianSections X).mapHomologicalComplex (.up ℕ)).map
        (forgottenResolutionMap X I)))) : QuasiIso q := by
  let : EnoughInjectives Y.Modules := enoughInjectives (X := Y)
  let G := SheafOfModules.forget Y.ringCatSheaf ⋙
    PresheafOfModules.evaluation Y.ringCatSheaf.obj (op (⊤ : Y.Opens))
  let V := forget₂ (ModuleCat.{u} (Y.ringCatSheaf.obj.obj (op (⊤ : Y.Opens))))
    AddCommGrpCat.{u}
  let : G.Additive := by dsimp [G]; infer_instance
  let : QuasiIso l := hl
  let (n : ℕ) : Injective (K.X n) := hK n
  have hG : QuasiIso ((G.mapHomologicalComplex (.up ℕ)).map l) :=
    G.quasiIso_map_of_rightAcyclic_nat l
      (fun n ↦ (module_pushforward_injective_acyclic f (I.cocomplex.X n)).2 ⊤)
      (fun n ↦ Functor.rightAcyclic_of_injective (K.X n))
  have hL : QuasiIso (((moduleSections Y).mapHomologicalComplex (.up ℕ)).map l) := by
    change QuasiIso ((V.mapHomologicalComplex (.up ℕ)).map
      ((G.mapHomologicalComplex (.up ℕ)).map l))
    rw [HomologicalComplex.quasiIso_map_iff_of_preservesHomology]
    exact hG
  have hR : QuasiIso (((abelianSections X).mapHomologicalComplex (.up ℕ)).map
      (forgottenResolutionMap X I)) := by
    let : QuasiIso (forgottenResolutionMap X I) := by
      delta forgottenResolutionMap
      infer_instance
    exact (abelianSections X).quasiIso_map_of_rightAcyclic_nat _
      (fun n ↦ forgottenInjectiveAcyclic X (I.cocomplex.X n))
      (fun n ↦ Functor.rightAcyclic_of_injective _)
  let := hL
  have hA : QuasiIso (a.hom ≫
      ((moduleSections Y).mapHomologicalComplex (.up ℕ)).map l) := quasiIso_comp _ _
  let := hA
  have hComp : QuasiIso ((a.hom ≫
      ((moduleSections Y).mapHomologicalComplex (.up ℕ)).map l) ≫ q) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap, hql.some.homologyMap_eq n]
    let := hR
    infer_instance
  let := hComp
  exact quasiIso_of_comp_left
    (a.hom ≫ ((moduleSections Y).mapHomologicalComplex (.up ℕ)).map l) q

/-- Two section-complex homotopies compare a module replacement with the abelian lift.
This asserts no equality involving Ext, and applies to any augmentation-compatible lift
(Stacks, Tags 01FB, 013P, 013S and 03FD). -/
theorem abelian_replacement_section_homotopies {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((pushforward f).obj F)) (K : CochainComplex Y.Modules ℕ)
    (hK : ∀ n : ℕ, Injective (K.X n))
    (l : ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K)
    (hl : QuasiIso l) (β : J.cocomplex ⟶ K)
    (hβ : J.ι.f 0 ≫ β.f 0 = (pushforward f).map (I.ι.f 0) ≫ l.f 0)
    (a : ((moduleSections X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ≅
      ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj
        (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex))
    (ha : ∀ n : ℕ, a.inv.f n = (presheaf (I.cocomplex.X n)).map
      (eqToHom (by simp) : (⊤ : X.Opens) ⟶ f ⁻¹ᵁ (⊤ : Y.Opens)).op) :
    ∃ q : ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj K ⟶
        ((abelianSections X).mapHomologicalComplex (.up ℕ)).obj
          (standardAbelianResolution X F).cocomplex,
      QuasiIso q ∧
      Nonempty (Homotopy
        (((moduleSections Y).mapHomologicalComplex (.up ℕ)).map β ≫ q)
        (counitSectionMap f F J)) ∧
      Nonempty (Homotopy
        ((a.hom ≫ ((moduleSections Y).mapHomologicalComplex (.up ℕ)).map l) ≫ q)
        (((abelianSections X).mapHomologicalComplex (.up ℕ)).map
          (forgottenResolutionMap X I))) := by
  obtain ⟨q, hqβ, hql⟩ := abelian_replacement_section_homotopies_core f I J K l hl β hβ a ha
  exact ⟨q, quasiIso_of_replacement_section_homotopy f I K hK l hl a q hql, hqβ, hql⟩

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
