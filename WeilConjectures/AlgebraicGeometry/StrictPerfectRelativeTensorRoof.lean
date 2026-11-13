/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictPerfectRelativeTensorComplex
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.RelativeTensorRoofComparison
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # A relative tensor representative roof

## References

* [Stacks Project, Tag 0DJQ](https://stacks.math.columbia.edu/tag/0DJQ)
* [Stacks Project, Tag 08CI](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Tag 06YH](https://stacks.math.columbia.edu/tag/06YH)
* [Stacks Project, Tag 05RT](https://stacks.math.columbia.edu/tag/05RT)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] CategoryTheory.module_overFunctor_preservesZero
  Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem common_quasiIso_roof
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K T : CochainComplex C ℤ} (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj T) :
    ∃ (H : CochainComplex C ℤ) (s : H ⟶ K) (t : H ⟶ T), QuasiIso s ∧ QuasiIso t := by
  obtain ⟨H, s, hs, t, ht⟩ := DerivedCategory.right_fac e.hom
  let := hs
  have heq : DerivedCategory.Q.map t = DerivedCategory.Q.map s ≫ e.hom := by
    rw [ht, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have htIso : IsIso (DerivedCategory.Q.map t) := by
    rw [heq]
    infer_instance
  exact ⟨H, s, t, (DerivedCategory.isIso_Q_map_iff_quasiIso C s).1 hs,
    (DerivedCategory.isIso_Q_map_iff_quasiIso C t).1 htIso⟩

namespace AlgebraicGeometry.Scheme

/-- The explicit local tensor and scalar-restricted K have a common quasi-isomorphic
complex. This is only the representative-comparison step; no relative flatness or
prescribed interval is assumed or asserted. -/
theorem strictPerfect_relativeTensor_roof
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X)
    (G K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eK : DerivedCategory.Q.obj K ≅ E ⊗ DerivedCategory.Q.obj G)
    (U : X.Opens)
    (L : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hL : IsStrictlyPerfect X U L)
    (eL : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj L) :
    let R := TopCat.Sheaf.inverseImageRing f.base S.sheaf
    let A := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R
    ∃ (H : CochainComplex (SheafOfModules.{u}
      ((sheafCompose ((Opens.grothendieckTopology X).over U)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))) ℤ)
      (s : H ⟶ ((SheafOfModules.overFunctor.{u} A U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.restrictScalars
              ((sheafCompose (Opens.grothendieckTopology X)
                (forget₂ CommRingCat.{u} RingCat.{u})).map
                  (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K))
      (t : H ⟶ strictPerfectRelativeTensorComplex f U L G),
      QuasiIso s ∧ QuasiIso t := by
  let R := TopCat.Sheaf.inverseImageRing f.base S.sheaf
  let A := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let C := SheafOfModules.{u} (A.over U)
  let : HasDerivedCategory.{u + 1} C := HasDerivedCategory.standard C
  obtain ⟨e⟩ := strictPerfect_relativeTensor_roof_comparison f E G K eK U L hL eL
  exact common_quasiIso_roof (C := C) e

end AlgebraicGeometry.Scheme
