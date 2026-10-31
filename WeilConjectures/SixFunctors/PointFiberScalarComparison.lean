/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.SixFunctors.ScalarSixTensorComparison
public import WeilConjectures.PoincareDuality.CondensedPointTensor
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings

/-! # Point-fibre scalar comparison datum

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
def-pod-mixed-support-cup-product.md, final sentence: compatibility with extension
of scalars along maps of admissible coefficient rings.
(blueprint: def-sf-point-fibre-scalar-comparison)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The induced ring map on singleton sections, namely precomposition on the tensor unit.
Source: the scalar-compatibility sentence of `def-pod-mixed-support-cup-product`
(blueprint: def-sf-point-fibre-scalar-comparison). -/
abbrev pointFiberScalarMap {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') :
    MonObj.Γ Λ.X →+* MonObj.Γ Λ'.X :=
  MonObj.Γ.map a.hom.hom

/-- Ordinary unbounded derived scalar extension on the singleton coefficient rings.
Its existing universal pair includes the K-flat normalized tensor and unit comparisons.
Source: the scalar-compatibility sentence of `def-pod-mixed-support-cup-product`
(blueprint: def-sf-point-fibre-scalar-comparison). -/
abbrev pointFiberScalarExtension {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') :=
  ModuleCat.ordinaryDerivedExtendScalars (pointFiberScalarMap a)

/-- The canonical source-side inverse tensorator, from the existing normalized
ordinary derived scalar extension. Source: the scalar-compatibility sentence of
`def-pod-mixed-support-cup-product` (blueprint: def-sf-point-fibre-scalar-comparison). -/
def pointFiberScalarTensor {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (M N : DerivedCategory (ModuleCat.{u + 1} (MonObj.Γ Λ.X))) :
    (pointFiberScalarExtension a).obj (M ⊗ N) ≅
      (pointFiberScalarExtension a).obj M ⊗ (pointFiberScalarExtension a).obj N :=
  (Functor.Monoidal.μIso (pointFiberScalarExtension a) M N).symm

/-- The canonical source-side unit comparison of the same strong monoidal structure.
Source: the scalar-compatibility sentence of `def-pod-mixed-support-cup-product`
(blueprint: def-sf-point-fibre-scalar-comparison). -/
def pointFiberScalarUnit {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') :
    (pointFiberScalarExtension a).obj (𝟙_ _) ≅ 𝟙_ _ :=
  (Functor.Monoidal.εIso (pointFiberScalarExtension a)).symm

/-- A specified natural isomorphism between scalar extension after the point fibre
and the point fibre after sheaf scalar extension. Both scalar functors carry their
fixed canonical strong monoidal structures: `pointFiberScalarExtension` retains its
normalized ordinary universal pair and `scalarSixChange` uses `scalarSixChangeMonoidal`.
The source tensor and unit are `pointFiberScalarTensor` and `pointFiberScalarUnit`;
the sheaf inverse tensorator is `scalarSixTensorIso a (Spec (.of k))`.
This datum makes no existence or scalar-coherence assertion.
Source: the final scalar-compatibility sentence of `def-pod-mixed-support-cup-product`
(blueprint: def-sf-point-fibre-scalar-comparison). -/
structure PointFiberScalarComparisonDatum (ell : ℕ) [Fact ell.Prime]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (_listed : IsListedScalarCoefficientMap ell a)
    (k : Type u) [Field k] [IsAlgClosed k] where
  /-- The specified scalar/point-fibre natural isomorphism. -/
  beta : TraceCupPoint.fiber Λ.X k ⋙ pointFiberScalarExtension a ≅
    scalarSixChange a (Spec (.of k)) ⋙ TraceCupPoint.fiber Λ'.X k

end AlgebraicGeometry.ProEtale.CondensedRing
