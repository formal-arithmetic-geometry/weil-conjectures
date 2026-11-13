/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure

import WeilConjectures.AlgebraicGeometry.StrictPerfectRelativeTensorTermsFlat
import WeilConjectures.AlgebraicGeometry.StrictPerfectRelativeTensorRoof
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # A bounded base-ring model on a strict-perfect tensor chart

## References

* [Stacks Project, Tag 0DJQ](https://stacks.math.columbia.edu/tag/0DJQ)
* [Stacks Project, Tag 08CI](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
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

namespace AlgebraicGeometry.Scheme

private theorem relativeTensorComplex_bound
    {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (L : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a b c d : ℤ)
    (hLb : ∀ n : ℤ, n < a ∨ b < n → IsZero (L.X n))
    (hGb : ∀ n : ℤ, n < c ∨ d < n → IsZero (G.X n)) :
    ∀ n : ℤ, n < a + c ∨ b + d < n →
      IsZero ((strictPerfectRelativeTensorComplex f U L G).X n) := by
  let : MonoidalCategory
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    SheafOfModules.monoidalCategory (X.sheaf.over U)
  let : (curriedTensor
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor (X.sheaf.over U)
  let (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :
      ((curriedTensor _).obj M).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj (X.sheaf.over U) M
  let GU := ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapHomologicalComplex
    (.up ℤ)).obj G
  let α := ((Opens.grothendieckTopology X).overPullback CommRingCat.{u} U).map
    (Modules.tensorPullbackRingMap f)
  let B := (sheafCompose ((Opens.grothendieckTopology X).over U)
    (forget₂ CommRingCat.{u} RingCat.{u})).map α
  intro n hn
  have hGU (q : ℤ) (hq : q < c ∨ d < q) : IsZero (GU.X q) :=
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).map_isZero
      (hGb q hq)
  have hz : IsZero ((CochainComplex.mapBifunctor L GU (curriedTensor _)).X n) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = n at hpq
    have ht : IsZero (L.X p ⊗ GU.X q) := by
      by_cases hp : p < a ∨ b < p
      · exact (tensorRight (GU.X q)).map_isZero (hLb p hp)
      · have hq : q < c ∨ d < q := by omega
        exact (tensorLeft (L.X p)).map_isZero (hGU q hq)
    exact ht.eq_of_src _ _
  exact (SheafOfModules.restrictScalars B).map_isZero hz

/-- A strict-perfect tensor chart admits a bounded K-flat model over the inverse-image
base ring, together with a common quasi-isomorphic complex connecting it to K restricted
on the chart. -/
theorem strictPerfect_relativeTensor_model
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
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj L)
    (a b c d : ℤ)
    (hLb : ∀ n : ℤ, n < a ∨ b < n → IsZero (L.X n))
    (hGb : ∀ n : ℤ, n < c ∨ d < n → IsZero (G.X n))
    (hGflat : ∀ n : ℤ, Modules.IsFlatOver (G.X n) f) :
    let R := TopCat.Sheaf.inverseImageRing f.base S.sheaf
    let A := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R
    ∃ (T H : CochainComplex (SheafOfModules.{u}
      ((sheafCompose ((Opens.grothendieckTopology X).over U)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))) ℤ),
      (∀ n : ℤ, n < a + c ∨ b + d < n → IsZero (T.X n)) ∧
      CochainComplex.IsKFlatTensor (R := R.over U) T ∧
      ∃ (s : H ⟶ ((SheafOfModules.overFunctor.{u} A U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.restrictScalars
              ((sheafCompose (Opens.grothendieckTopology X)
                (forget₂ CommRingCat.{u} RingCat.{u})).map
                  (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) (t : H ⟶ T),
        QuasiIso s ∧ QuasiIso t := by
  let T := strictPerfectRelativeTensorComplex f U L G
  have hTb : ∀ n : ℤ, n < a + c ∨ b + d < n → IsZero (T.X n) :=
    relativeTensorComplex_bound f U L G a b c d hLb hGb
  have hTf := strictPerfect_relativeTensor_terms_flat f U L G hL hGflat
  have hTk : CochainComplex.IsKFlatTensor
      (R := (TopCat.Sheaf.inverseImageRing f.base S.sheaf).over U) T :=
    CochainComplex.isKFlat_of_boundedAbove_flat T
      ⟨b + d, fun n hn ↦ hTb n (Or.inr hn)⟩ hTf
  obtain ⟨H, s, t, hs, ht⟩ := strictPerfect_relativeTensor_roof f E G K eK U L hL eL
  exact ⟨T, H, hTb, hTk, s, t, hs, ht⟩

end AlgebraicGeometry.Scheme
