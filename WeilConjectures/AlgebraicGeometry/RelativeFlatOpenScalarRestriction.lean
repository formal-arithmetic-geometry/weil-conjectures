/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.RelativeFlatModuleStalk
import WeilConjectures.AlgebraicGeometry.OpenScalarRestrictionStalkCriterion
import WeilConjectures.AlgebraicGeometry.InverseImageStructureStalkIso
import Mathlib.RingTheory.RingHom.Flat

/-! # Relative flatness on an open localized site

## References

* [Stacks Project, Tag 01U2](https://stacks.math.columbia.edu/tag/01U2)
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory TopologicalSpace
namespace AlgebraicGeometry.Scheme

/-- Restricting an affine-locally base-flat module to an open site and restricting
scalars along the inverse-image structure map yields a flat module over that ring. -/
theorem relativeFlat_open_scalarRestriction
    {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (G : X.Modules)
    (hflat : G.IsFlatOver f) :
    let α := ((Opens.grothendieckTopology X).overPullback CommRingCat.{u} U).map
      (Modules.tensorPullbackRingMap f)
    let B := (sheafCompose ((Opens.grothendieckTopology X).over U)
      (forget₂ CommRingCat.{u} RingCat.{u})).map α
    SheafOfModules.IsFlat ((SheafOfModules.restrictScalars B).obj
      ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).obj G)) := by
  apply RingedSpace.isFlat_open_scalarRestriction_of_stalks X.toRingedSpace
    (TopCat.Sheaf.inverseImageRing f.base S.sheaf) (Modules.tensorPullbackRingMap f)
  intro x hx
  let A := S.presheaf.stalk (f x)
  let B := (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).obj
    (TopCat.Sheaf.inverseImageRing f.base S.sheaf).obj
  let C := X.presheaf.stalk x
  let ψ : B ⟶ C := (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
    (Modules.tensorPullbackRingMap f).hom
  let M := (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G
  obtain ⟨e, he⟩ := exists_inverseImageStructure_stalk_iso f x
  let : Algebra A C := (f.stalkMap x).hom.toAlgebra
  have hM := relative_flat_module_stalk f G hflat x rfl
  let N := (ModuleCat.restrictScalars ψ.hom).obj M
  let : Algebra B A := e.inv.hom.toAlgebra
  let : Module A N := Module.compHom M (f.stalkMap x).hom
  have : IsScalarTower B A N := by
    constructor
    intro b a m
    change (f.stalkMap x).hom (e.inv.hom b * a) • m =
      ψ.hom b • ((f.stalkMap x).hom a • m)
    rw [map_mul, mul_smul]
    congr 1
    have hc : e.inv ≫ f.stalkMap x = ψ := by
      rw [← he]
      simp only [Iso.inv_hom_id_assoc]
      rfl
    exact ConcreteCategory.congr_hom hc b
  have : Module.Flat A N := hM
  have : Module.Flat B A := RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso e.inv)
  exact Module.Flat.trans B A N

end AlgebraicGeometry.Scheme
