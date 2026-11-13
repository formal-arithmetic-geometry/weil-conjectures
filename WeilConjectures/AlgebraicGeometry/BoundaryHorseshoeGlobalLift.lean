/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
@[expose] public section
universe u wC wD
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero lift and degree-one cycle in a global horseshoe resolution.
Source: Stacks Project, Tags 0117, 013T and 015B. -/
theorem boundary_horseshoe_global_lift (X : Scheme.{u})
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    [EnoughInjectives X.Modules]
    [EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [(RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive]
    (S : ShortComplex X.Modules) (IA : InjectiveResolution S.X₁)
    (IB : InjectiveResolution S.X₂) (IC : InjectiveResolution S.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (_hιA : IA.ι ≫ α = (CochainComplex.single₀ X.Modules).map S.f ≫ IB.ι)
    (_hιB : IB.ι ≫ β = (CochainComplex.single₀ X.Modules).map S.g ≫ IC.ι)
    (hrows : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval X.Modules (ComplexShape.up ℕ) k)).ShortExact)
    (_hS : S.ShortExact) (q : S.X₃.val.obj (op ⊤)) :
    ∃ (b : (IB.cocomplex.X 0).val.obj (op ⊤))
      (a : (RingedSpace.globalSectionsComplex IA).cycles 1),
      (β.f 0).val.app (op ⊤) b = (IC.ι.f 0).val.app (op ⊤) q ∧
      (α.f 1).val.app (op ⊤)
        ((RingedSpace.globalSectionsComplex IA).iCycles 1 a) =
          (IB.cocomplex.d 0 1).val.app (op ⊤) b := by
  let v := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let H := (ShortComplex.mk α β hαβ).map
    (v.mapHomologicalComplex (ComplexShape.up ℕ))
  have hH : H.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro k
    have hr := hrows k
    change (ShortComplex.mk (α.f k) (β.f k) _).ShortExact at hr
    exact (hr.splittingOfInjective.map v).shortExact
  have hr (k : ℕ) : (H.map (HomologicalComplex.eval _ _ k)).ShortExact := by
    have h := hrows k
    change (ShortComplex.mk (α.f k) (β.f k) _).ShortExact at h
    exact (h.splittingOfInjective.map v).shortExact
  obtain ⟨b, hb⟩ := (hr 0).moduleCat_surjective_g ((IC.ι.f 0).val.app (op ⊤) q)
  have hz : (H.X₃.d 0 1) ((IC.ι.f 0).val.app (op ⊤) q) = 0 := by
    change (v.map (IC.ι.f 0) ≫ v.map (IC.cocomplex.d 0 1)) q = 0
    rw [← v.map_comp, IC.ι_f_zero_comp_complex_d, v.map_zero]
    rfl
  change (H.g.f 0) b = (IC.ι.f 0).val.app (op ⊤) q at hb
  have hdb : (H.g.f 1) (H.X₂.d 0 1 b) = 0 := by
    have he := congrArg (fun f ↦ f b) (H.g.comm 0 1)
    simpa only [ModuleCat.comp_apply, hb, hz] using he.symm
  obtain ⟨x, hx⟩ := ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (hr 1).exact) _ |>.mp hdb
  have hdx := ShortComplex.ShortExact.d_eq_zero_of_f_eq_d_apply hH 0 1 b x hx 2
  let a := H.X₁.cyclesMk x 2 ((ComplexShape.up ℕ).next_eq' rfl) hdx
  refine ⟨b, a, hb, ?_⟩
  have hai : H.X₁.iCycles 1 a = x :=
    HomologicalComplex.i_cyclesMk H.X₁ x 2 ((ComplexShape.up ℕ).next_eq' rfl) hdx
  change (H.f.f 1) (H.X₁.iCycles 1 a) = H.X₂.d 0 1 b
  rw [hai]
  exact hx
end AlgebraicGeometry.Scheme.Modules
