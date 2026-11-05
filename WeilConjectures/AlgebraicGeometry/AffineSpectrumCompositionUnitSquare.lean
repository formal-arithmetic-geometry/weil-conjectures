/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates

/-! # Affine spectrum composition unit square

Source: Stacks Project, Tag 0D5S, composition coherence used in the affine reduction.
(blueprint: lem-pc-affine-spectrum-composition-unit-square).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w z
open CategoryTheory
-- Prove the coherence calculation with abstract functors, so its algebra does not
-- unfold the constructions of derived categories or derived pullback.
namespace AffineSpectrumCoherence
variable {S : Type u} [Category.{v} S]
  {D : S → Type w} [∀ X, Category.{z} (D X)]
  (F : ∀ {X Y : S}, (X ⟶ Y) → (D Y ⥤ D X))
  (c : ∀ {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z), F g ⋙ F f ≅ F (f ≫ g))
  (i : ∀ X : S, F (𝟙 X) ≅ 𝟭 (D X))

end AffineSpectrumCoherence

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
attribute [local implicit_reducible] Scheme.isoSpec asIso
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  Functor.mapHomologicalComplex HomotopyCategory Functor.mapHomotopyCategory
  HomotopyCategory.quotient DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

end AlgebraicGeometry
