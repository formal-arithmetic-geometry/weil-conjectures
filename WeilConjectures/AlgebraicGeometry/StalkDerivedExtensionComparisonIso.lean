/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
import WeilConjectures.AlgebraicGeometry.StalkDerivedExtensionComparisonIsoCore
import WeilConjectures.AlgebraicGeometry.StalkDerivedExtensionComparisonIsIso

/-! Intermediate comparison isomorphism for the derived stalk extension.
(blueprint: lem-pc-stalk-derived-extension-comparison-intermediate) -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.SingleComplexBaseChange

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

end AlgebraicGeometry.SingleComplexBaseChange
