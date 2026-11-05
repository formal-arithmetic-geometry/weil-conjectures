/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageData
import WeilConjectures.CategoryTheory.Finite.FinitePowerComplex
import all WeilConjectures.Algebra.Homology.Finite.FiniteFreeScalarExtension
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Finite-free coordinates for a specified scalar presentation

Source: Stacks Project, Tags 03EK and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

set_option maxHeartbeats 2000000 in
-- Elaborating the presentation transport and tensor coordinates requires extra heartbeats.
/-- The tensor coordinates transported through the specified ordinary presentation.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sp-finite-free-presented-scalar-coordinates). -/
@[irreducible] private def presentedFiniteFreeCoordinates (X : Scheme.{u})
    (s : ScalarModel X) {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (d : ℕ)
    (θ : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≅
      (proEtaleRingRestrictScalars a).obj (SheafOfModules.unit ((sheafCompose
        (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))) :
    (s.presentation a).ordinary ⋙ proEtaleRingRestrictScalars a ≅
      Functor.const (Discrete (Fin d)) ⋙ lim :=
  NatIso.ofComponents (fun M ↦ (proEtaleRingRestrictScalars a).mapIso
    (eqToIso ((s.presentation a).obj_eq M)) ≪≫
      SheafOfModules.scalarExtensionIso a d θ M) (by
    intro M N f
    let p := s.presentation a
    let U := proEtaleRingRestrictScalars a
    change U.map (p.ordinary.map f) ≫ U.map (eqToHom (p.obj_eq N)) ≫
      (SheafOfModules.scalarExtensionIso a d θ N).hom =
      U.map (eqToHom (p.obj_eq M)) ≫
        (SheafOfModules.scalarExtensionIso a d θ M).hom ≫ _
    rw [← U.map_comp_assoc]
    have hm : p.ordinary.map f ≫ eqToHom (p.obj_eq N) =
        eqToHom (p.obj_eq M) ≫ SheafOfModules.changeOfRingsHom a M f := by
      rw [p.map_eq]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [hm, U.map_comp, Category.assoc,
      SheafOfModules.scalarExtensionIso_naturality a d θ f]
    apply congrArg (fun g ↦ U.map (eqToHom (p.obj_eq M)) ≫
      (SheafOfModules.scalarExtensionIso a d θ M).hom ≫ g)
    apply Pi.hom_ext
    intro i
    erw [Pi.map_π])

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
