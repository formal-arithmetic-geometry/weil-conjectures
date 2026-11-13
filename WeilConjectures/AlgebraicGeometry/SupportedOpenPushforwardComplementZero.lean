/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import all WeilConjectures.AlgebraicGeometry.PerfectRestrictionClassesSmall
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Vanishing of open pushforward on the complement of closed support

## References

* [Stacks Project, Tag 08DP](https://stacks.math.columbia.edu/tag/08DP)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem isZero_of_zero_stalks (Y : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (hM : ∀ y : Y, Subsingleton (↑(TopCat.Presheaf.stalk M.val.presheaf y))) :
    IsZero M := by
  let G := SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)
  have hG : IsZero (G.obj M) := by
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero (G.obj M)).mpr
    intro y
    exact AddCommGrpCat.isZero_iff_subsingleton.mpr (hM y)
  apply (IsZero.iff_id_eq_zero M).mpr
  apply G.map_injective
  rw [G.map_id, G.map_zero]
  exact (IsZero.iff_id_eq_zero (G.obj M)).mp hG


/-- Derived open pushforward vanishes on an open disjoint from the cohomological support. -/
theorem supported_open_pushforward_complement_zero (X : Scheme.{u}) (U : X.Opens)
    (T : Set X) (V : X.Opens) (hV : ∀ x : X, x ∈ V → x ∉ T)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (F : schemeDerivedCategory U.toScheme)
    (hs : ∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj F).val.presheaf x))) :
    IsZero ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj
        ((schemeDerivedDirectImage U.ι).obj F)) := by
  classical
  let W := U.ι ⁻¹ᵁ V
  let eW := Modules.overEquiv W
  let eV := Modules.overEquiv V
  obtain ⟨hDW⟩ := hasDerivedCategory_of_equivalence eW.symm
  let : HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) := hDW
  obtain ⟨hDV⟩ := hasDerivedCategory_of_equivalence eV.symm
  let : HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) := hDV
  let rW := schemeOpenRestriction U.toScheme W
  have hzW : IsZero (rW.mapDerivedCategory.obj F) := by
    apply DerivedCategory.isZero_of_forall_isZero_homology
    intro n
    let M := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj F
    have hzM : IsZero (rW.obj M) := by
      let i := (Modules.overFunctorEquiv W).app M
      refine (show IsZero ((Modules.restrictFunctor W.ι).obj M) from ?_).of_iso i
      apply isZero_of_zero_stalks W.toScheme
      intro y
      let j := (Modules.restrictStalkNatIso W.ι y).app M
      have h := hs n y.val (hV y.val.val y.property)
      exact j.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr h
    exact hzM.of_iso ((rW.mapDerivedCategoryHomologyFunctorIso n).app F).symm
  obtain ⟨comparison⟩ := schemeDerivedDirectImage_openRestriction U.ι V
  have : (schemeDerivedDirectImage (U.ι ∣_ V)).Additive := by
    dsimp [schemeDerivedDirectImage, RingedSpace.derivedModuleDirectImage]
    infer_instance
  have hzV : IsZero ((schemeOpenRestriction X V).mapDerivedCategory.obj
      ((schemeDerivedDirectImage U.ι).obj F)) := by
    exact ((schemeDerivedDirectImage (U.ι ∣_ V)).map_isZero hzW).of_iso
      (comparison.app F)
  let rV := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V
  have : eV.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : eV.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let dV := eV.mapDerivedCategory
  have hzV' : IsZero (dV.functor.obj
      (rV.mapDerivedCategory.obj ((schemeDerivedDirectImage U.ι).obj F))) :=
    hzV.of_iso ((Functor.mapDerivedCategoryCompIso rV eV.functor).symm.app _).symm
  exact IsZero.of_full_of_faithful_of_isZero dV.functor _ hzV'


end AlgebraicGeometry.Scheme
