/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.ModuleCupRealizationComplexData

/-! # Cochain obligations for resolution pairings

Source: Stacks Project, Tag 0FKU, construction before Lemma 20.31.3.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {X : Scheme.{u}}
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

attribute [local instance] cupRealizationMonoidalCategory cupRealizationSymmetricCategory
  cupRealizationHasColimitsOfSize cupRealizationMonoidalPreadditive cupRealizationMonoidalClosed
  cupRealizationHasFunctorialFlatResolution cupRealizationIsGrothendieckAbelian
  cupRealizationDerivedMonoidal cupRealizationQLax

/-- A cochain realization exists.
Source: Stacks Project, Tag 0FKU, construction before Lemma 20.31.3.
Proof: use the sheaf tensor universal property to descend the restriction-compatible
bilinear section maps in each nonnegative bidegree. Assemble these maps on the coproduct
terms of the total tensor. The Leibniz identity gives the differential compatibility.
Negative-degree factors are zero, so extend those summands by zero. The coproduct
inclusion formula is exactly the section formula in Realizes.
(blueprint: lem-sc-module-cup-resolution-existence) -/
theorem moduleCup_resolution_realization_exists {F G : X.Modules} (D : CupResolutionPairing F G) :
    ∃ t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex,
      D.Realizes t := by
  sorry


end
end AlgebraicGeometry.Scheme.Modules
