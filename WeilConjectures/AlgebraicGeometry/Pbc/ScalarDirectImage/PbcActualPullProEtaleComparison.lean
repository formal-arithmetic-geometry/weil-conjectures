/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerDirectImageSupplement

/-! # Actual completed pullback versus the canonical pro-étale ring pullback

The actual completed module pullback `pbcActualModulePull g d` and the canonical pro-étale
ring pullback along the invertible completed coefficient map agree, by the object equality
of the scalar-extension interface. Their derived functors are left adjoints of the same
derived direct image, and the comparison is compatible with both derived adjunctions.

Source: Stacks Tags 03D2, 099N and 0D6D
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

/-- The completed coefficient map is invertible.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
theorem pbcCompletedCoefficientMap_isIso : IsIso (completedCoefficientMap g d) :=
  completedCoefficient_isIso g d

/-- The completed coefficient map, as an isomorphism of ring sheaves.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
abbrev pbcActualCoefficientIso :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (pbcAdicCompletion Y d) ≅
      pbcAdicCompletion X d :=
  letI := pbcCompletedCoefficientMap_isIso g d
  asIso (completedCoefficientMap g d)

@[simp]
theorem pbcActualCoefficientIso_hom :
    (pbcActualCoefficientIso g d).hom = completedCoefficientMap g d := rfl

/-- The actual derived direct image is the canonical pro-étale derived direct image.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
theorem pbcActualDerivedPush_eq :
    pbcActualDerivedPush g d = proEtaleRingDerivedDirectImage g (pbcAdicCompletion Y d)
      (pbcAdicCompletion X d) (pbcActualCoefficientIso g d) := rfl

/-- The object equality of the scalar-extension interface, as a natural isomorphism of
module pullbacks. Source: Stacks Tag 03EK
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
def pbcActualModulePullIso :
    pbcActualModulePull g d ≅ proEtaleRingModulePullback g (pbcAdicCompletion Y d)
      (pbcAdicCompletion X d) (pbcActualCoefficientIso g d) :=
  sorry

/-- The derived comparison between the actual derived pullback and the canonical one,
retaining the universal counit on every complex.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
def pbcActualPullProEtaleIso :
    pbcActualDerivedPull g d ≅ proEtaleRingDerivedPullback g (pbcAdicCompletion Y d)
      (pbcAdicCompletion X d) (pbcActualCoefficientIso g d) :=
  sorry

/-- The derived comparison is the ordinary module comparison on every complex.
Source: Stacks Tag 099N (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
theorem pbcActualPullProEtaleIso_fac
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :
    (pbcActualPullProEtaleIso g d).hom.app (DerivedCategory.Q.obj P) ≫
        (proEtaleRingDerivedPullbackFactors g (pbcAdicCompletion Y d)
          (pbcAdicCompletion X d) (pbcActualCoefficientIso g d)).hom.app P =
      pbcActualPullComplexCounit g d P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (pbcActualModulePullIso g d) (.up ℤ)).hom.app P) := by
  sorry

/-- The comparison intertwines the actual derived adjunction with the canonical one.
Source: Stacks Tags 03D2 and 099N
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
theorem pbcActualDerivedAdjunction_homEquiv
    (M : PbcCompletedDerived Y d) (N : PbcCompletedDerived X d)
    (t : (pbcActualDerivedPull g d).obj M ⟶ N) :
    (pbcActualDerivedAdjunction g d).homEquiv M N t =
      (proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (pbcActualCoefficientIso g d)).homEquiv M N
          ((pbcActualPullProEtaleIso g d).inv.app M ≫ t) := by
  sorry

end AlgebraicGeometry.Scheme
