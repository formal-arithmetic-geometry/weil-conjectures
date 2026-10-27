/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Closed substacks with their scheme base changes

Source: Stacks Project, stacks-properties.tex, definition-substacks and Tag 0507
(blueprint: def-sfb-closed-moduli-substack).

Full subcategories and inclusions reuse the open-substack module's general constructions.
Closedness is tested on the actual projection from each scheme 2-base change.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ w₁ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- A scheme represents a 2-base change with its specified projection to the test scheme:
some comparison functor is a scheme presentation in the sense of the recorded
`IsSchemeModuliBaseChange` (def-sfb-moduli-chart-normalization).
Source: Stacks Project, Tag 003R and Tag 0507
(blueprint: def-sfb-closed-moduli-substack). -/
def HasSchemeModuliBaseChange {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) (T : Over S)
    (t : BasedFunctor (discreteModuli (yoneda.obj T)) G) (Z : Over S) (j : Z ⟶ T) : Prop :=
  ∃ e : BasedFunctor (discreteModuli (yoneda.obj Z)) (moduliTwoFiberProduct t f),
    IsSchemeModuliBaseChange e j

/-- A strictly full substack with representable closed-immersion inclusion.
Stability under every arrow gives pullback stability and closure under isomorphisms;
the full subcategory retains all arrows. The stack field asserts étale descent.
Source: Stacks Project, definition-substacks and Tag 0507
(blueprint: def-sfb-closed-moduli-substack). -/
structure ClosedModuliSubstack {S : Scheme.{u}} (F : BasedCategory.{v₁, w₁} (Over S)) where
  property : F.obj → Prop
  pullback : ∀ {x y : F.obj} (_f : x ⟶ y), property y → property x
  stack : IsModuliStack (fullModuliSubcategory F property)
  closed_pullback : ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
    ∃ (Z : Over S) (j : Z ⟶ T), IsClosedImmersion j.left ∧
      HasSchemeModuliBaseChange (fullModuliInclusion F property) T t Z j

/-- The full closed substack, with its original projection to schemes.
Source: Stacks Project, definition-substacks
(blueprint: def-sfb-closed-moduli-substack). -/
def ClosedModuliSubstack.category {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} (W : ClosedModuliSubstack F) :
    BasedCategory (Over S) :=
  fullModuliSubcategory F W.property

/-- The actual full inclusion of a closed substack.
Source: Stacks Project, definition-substacks
(blueprint: def-sfb-closed-moduli-substack). -/
def ClosedModuliSubstack.inclusion {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} (W : ClosedModuliSubstack F) :
    BasedFunctor W.category F :=
  fullModuliInclusion F W.property

end CategoryTheory
