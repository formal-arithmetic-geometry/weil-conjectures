/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.ConcreteCategory
import WeilConjectures.CategoryTheory.Abelian.RightDerivedTriangleConnecting
@[expose] public section
universe u wC wD
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option maxHeartbeats 600000 in
-- Comparing X.Modules with module sheaves makes the isomorphism transports expensive.
set_option backward.isDefEq.respectTransparency false in
/-- The snake boundary of the global horseshoe equals the derived-triangle boundary.
Source: Stacks Project, Tags 0117, 013T and 015B. -/
theorem boundary_horseshoe_boundary_identification (X : Scheme.{u})
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    [EnoughInjectives X.Modules]
    [EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [(RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive]
    (S : ShortComplex X.Modules) (IA : InjectiveResolution S.X₁)
    (IB : InjectiveResolution S.X₂) (IC : InjectiveResolution S.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (hιA : IA.ι ≫ α = (CochainComplex.single₀ X.Modules).map S.f ≫ IB.ι)
    (hιB : IB.ι ≫ β = (CochainComplex.single₀ X.Modules).map S.g ≫ IC.ι)
    (hrows : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval X.Modules (ComplexShape.up ℕ) k)).ShortExact)
    (hS : S.ShortExact) (q : S.X₃.val.obj (op ⊤))
    (b : (IB.cocomplex.X 0).val.obj (op ⊤))
    (a : (RingedSpace.globalSectionsComplex IA).cycles 1)
    (hb : (β.f 0).val.app (op ⊤) b = (IC.ι.f 0).val.app (op ⊤) q)
    (ha : (α.f 1).val.app (op ⊤)
      ((RingedSpace.globalSectionsComplex IA).iCycles 1 a) =
        (IB.cocomplex.d 0 1).val.app (op ⊤) b) :
    (IA.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 1).hom
      (RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app S.X₃ q)) =
      (RingedSpace.globalSectionsComplex IA).homologyπ 1 a := by
  let v : X.Modules ⥤
      ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
    RingedSpace.globalSectionsFunctor X.toRingedSpace
  let : HasDerivedCategory.{wC} X.Modules :=
    inferInstanceAs (HasDerivedCategory.{wC}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  let : PreservesFiniteLimits v :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings X.toRingedSpace) (op ⊤)))
  obtain ⟨G, hF, hhorse, htriangle⟩ := rightDerived_triangle_connecting v
  obtain ⟨hH, hδ⟩ := hhorse S hS IA IB IC α β hαβ hιA hιB hrows
  have ht := htriangle S hS 0
  have hd := hδ 0
  have hcompare : RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0 ≫
      (IA.isoRightDerivedObj v 1).hom =
      (IC.isoRightDerivedObj v 0).hom ≫ hH.δ 0 1 rfl := by
    apply (cancel_mono (IA.isoRightDerivedObj v 1).inv).1
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply (cancel_epi
      (eqToHom (congrArg (fun F ↦ (F 0).obj S.X₃) hF))).1
    erw [← hd]
    apply (cancel_mono
      (v.homologyRightDerivedFunctorPlusObjSingleFunctorIso S.X₁ 1).inv).1
    simp only [Category.assoc]
    erw [ht]
    simp only [RingedSpace.moduleCohomologyBoundary,
      Functor.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso,
      NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, Category.assoc]
    dsimp only [v]
    erw [Iso.hom_inv_id, Category.comp_id]
  let H := (ShortComplex.mk α β hαβ).map
    (v.mapHomologicalComplex (ComplexShape.up ℕ))
  let z := IC.toRightDerivedZero' v q
  have hz : H.X₃.iCycles 0 z = (IC.ι.f 0).val.app (op ⊤) q := by
    change (IC.toRightDerivedZero' v ≫ H.X₃.iCycles 0) q = _
    erw [InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    rfl
  have hzero : H.X₃.d 0 1 ((IC.ι.f 0).val.app (op ⊤) q) = 0 := by
    change (v.map (IC.ι.f 0) ≫ v.map (IC.cocomplex.d 0 1)) q = 0
    rw [← v.map_comp, IC.ι_f_zero_comp_complex_d, v.map_zero]
    rfl
  have hsnake := hH.δ_apply 0 1 rfl
    ((IC.ι.f 0).val.app (op ⊤) q) hzero b hb
    (H.X₁.iCycles 1 a) ha 2 ((ComplexShape.up ℕ).next_eq' rfl)
  have hza : H.X₃.cyclesMk ((IC.ι.f 0).val.app (op ⊤) q) 1
      ((ComplexShape.up ℕ).next_eq' rfl) hzero = z := by
    apply (Preadditive.mono_iff_injective (H.X₃.iCycles 0)).1 inferInstance
    rw [HomologicalComplex.i_cyclesMk]
    exact hz.symm
  have haa : H.X₁.cyclesMk (H.X₁.iCycles 1 a) 2 ((ComplexShape.up ℕ).next_eq' rfl)
      (ShortComplex.ShortExact.d_eq_zero_of_f_eq_d_apply hH 0 1 b
        (H.X₁.iCycles 1 a) ha 2) = a := by
    apply (Preadditive.mono_iff_injective (H.X₁.iCycles 1)).1 inferInstance
    rw [HomologicalComplex.i_cyclesMk]
    rfl
  rw [hza, haa] at hsnake
  have haug : v.toRightDerivedZero.app S.X₃ ≫ (IC.isoRightDerivedObj v 0).hom =
      IC.toRightDerivedZero' v ≫ H.X₃.homologyπ 0 := by
    erw [IC.toRightDerivedZero_eq v]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  change ((v.toRightDerivedZero.app S.X₃ ≫
    RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0) ≫
      (IA.isoRightDerivedObj v 1).hom) q = _
  erw [Category.assoc, hcompare, ← Category.assoc, haug]
  exact hsnake
end AlgebraicGeometry.Scheme.Modules
