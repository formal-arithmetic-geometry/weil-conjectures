/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupPoint.CondensedPointTensor
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings

/-! # Condensed point-fibre tensor-system datum

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
def-pod-mixed-support-cup-product.md, definition of the condensed mixed-support cup
product and its final scalar-extension compatibility sentence
(blueprint: def-sf-point-fibre-tensor-system).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint

/-- The localized degree-zero unit of the normalized point-fibre tensor data.
Source: the normalized point-fibre tensor and unit in
`def-pod-condensed-point-tensor` (blueprint: def-sf-point-fibre-tensor-system). -/
def pointFiberUnit {Λ : ScalarSixRing.{u}} (k : Type u) [Field k] [IsAlgClosed k] :
    𝟙_ (DerivedCategory (ModuleCat.{u + 1} (MonObj.Γ Λ.X))) ⟶
      (fiber Λ.X k).obj
        (𝟙_ (DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
            (condensedRingObj Λ.X (Spec (.of k)))))) :=
  (tensorData Λ.X k).derived.ε ≫ (exactComparison Λ.X k).inv.app _

end AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint
