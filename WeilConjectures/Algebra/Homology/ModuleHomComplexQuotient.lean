/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.CategoryTheory.Linear.Basic

/-! # Module Hom homology as homotopy classes

## References

* Stacks Project, Tag 0A8H
* Mathlib `HomComplexCohomology`, `homAddEquiv` and `leftHomologyData`
-/

@[expose] public section

universe u
open CategoryTheory
namespace CochainComplex

set_option backward.isDefEq.respectTransparency false in
/-- Homotopy classes of module-complex maps are degree-zero module Hom homology. -/
theorem moduleHomComplex_quotient (A : Type u) [CommRing A] :
    ∃ b : ∀ (L M : CochainComplex (ModuleCat.{u} A) ℤ),
        ((HomotopyCategory.quotient _ _).obj L ⟶
          (HomotopyCategory.quotient _ _).obj M) ≃+
          (moduleHomComplex L M).homology 0,
      ∀ (L M : CochainComplex (ModuleCat.{u} A) ℤ) (f : L ⟶ M),
        ∃ z : (moduleHomComplex L M).cycles 0,
          (moduleHomComplex L M).iCycles 0 z = HomComplex.Cochain.ofHom f ∧
          b L M ((HomotopyCategory.quotient _ _).map f) =
            (moduleHomComplex L M).homologyπ 0 z := by
  classical
  let U := forget₂ (ModuleCat.{u} A) AddCommGrpCat
  let H := HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)
  let q (L M : CochainComplex (ModuleCat.{u} A) ℤ) :
      U.obj ((moduleHomComplex L M).homology 0) ≅
        AddCommGrpCat.of (HomComplex.CohomologyClass L M 0) :=
    let D₀ := ((moduleHomComplex L M).sc 0).homologyData.left
    U.mapIso D₀.homologyIso ≪≫ (D₀.map U).homologyIso.symm ≪≫
      (HomComplex.leftHomologyData L M 0).homologyIso
  let j (L M : CochainComplex (ModuleCat.{u} A) ℤ) :
      HomComplex.CohomologyClass L M 0 ≃+ (H.obj L ⟶ H.obj M) :=
    (HomComplex.CohomologyClass.homAddEquiv (K := L) (L := M) (n := 0)).trans
      (Linear.homCongr ℤ (Iso.refl _) (H.mapIso ((shiftFunctorZero _ ℤ).app M))).toAddEquiv
  let b (L M : CochainComplex (ModuleCat.{u} A) ℤ) :=
    (j L M).symm.trans (q L M).addCommGroupIsoToAddEquiv.symm
  refine ⟨b, ?_⟩
  intro L M f
  let z : (moduleHomComplex L M).cycles 0 :=
    (moduleHomComplex L M).cyclesMk (HomComplex.Cochain.ofHom f) 1 (by simp)
      (HomComplex.δ_ofHom f)
  have hz : (moduleHomComplex L M).iCycles 0 z = HomComplex.Cochain.ofHom f :=
    (moduleHomComplex L M).i_cyclesMk _ 1 (by simp) (HomComplex.δ_ofHom f)
  refine ⟨z, hz, ?_⟩
  apply (q L M).addCommGroupIsoToAddEquiv.injective
  change (q L M).addCommGroupIsoToAddEquiv
      ((q L M).addCommGroupIsoToAddEquiv.symm ((j L M).symm (H.map f))) = _
  rw [AddEquiv.apply_symm_apply]
  apply (j L M).injective
  rw [AddEquiv.apply_symm_apply]
  have hq : (q L M).hom ((moduleHomComplex L M).homologyπ 0 z) =
      HomComplex.CohomologyClass.mk (HomComplex.Cocycle.ofHom f) := by
    let S := (moduleHomComplex L M).sc 0
    let D := HomComplex.leftHomologyData L M 0
    let E := S.homologyData.left.map U
    let x : E.K := U.map S.homologyData.left.cyclesIso.hom z
    have hx : E.i x = HomComplex.Cochain.ofHom f := by
      have hh := ConcreteCategory.congr_hom
        (U.congr_map S.homologyData.left.cyclesIso_hom_comp_i) z
      exact hh.trans hz
    have hproj : U.map S.homologyData.left.homologyIso.hom
        (U.map S.homologyπ z) = E.π x := by
      exact ConcreteCategory.congr_hom
        (U.congr_map S.homologyData.left.homologyπ_comp_homologyIso_hom) z
    change D.homologyIso.hom (E.homologyIso.inv
      (U.map S.homologyData.left.homologyIso.hom (U.map S.homologyπ z))) = _
    rw [hproj]
    have he := ConcreteCategory.congr_hom E.π_comp_homologyIso_inv x
    dsimp at he
    rw [he]
    have hd := ConcreteCategory.congr_hom D.homologyπ_comp_homologyIso_hom
      (E.cyclesIso.inv x)
    dsimp at hd
    change D.homologyIso.hom
      ((HomComplex L M).sc 0 |>.homologyπ (E.cyclesIso.inv x)) = _
    rw [hd]
    have hy : D.cyclesIso.hom (E.cyclesIso.inv x) = HomComplex.Cocycle.ofHom f := by
      apply HomComplex.Cocycle.ext
      have hd' := ConcreteCategory.congr_hom D.cyclesIso_hom_comp_i
        (E.cyclesIso.inv x)
      have he' := ConcreteCategory.congr_hom E.cyclesIso_inv_comp_iCycles x
      exact hd'.trans (he'.trans hx)
    rw [hy]
    rfl
  change H.map f = j L M ((q L M).hom ((moduleHomComplex L M).homologyπ 0 z))
  rw [hq]
  change H.map f = (𝟙 _ ≫ H.map
    (HomComplex.Cocycle.equivHomShift.symm (HomComplex.Cocycle.ofHom f))) ≫
      H.map ((shiftFunctorZero _ ℤ).hom.app M)
  rw [Category.id_comp, ← H.map_comp]
  congr 1
  ext p
  simp [HomComplex.Cocycle.equivHomShift_symm_apply,
    HomComplex.Cocycle.homOf, HomComplex.Cocycle.rightShift,
    HomComplex.Cochain.rightShift_v, CochainComplex.shiftFunctorZero_hom_app_f]

end CochainComplex
