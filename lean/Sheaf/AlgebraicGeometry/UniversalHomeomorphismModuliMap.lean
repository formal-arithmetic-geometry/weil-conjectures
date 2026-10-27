/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen

/-! # Universal homeomorphisms of algebraic stacks

Source: Stacks Project, Morphisms of Stacks, Tag 0CI7
(blueprint: def-sfb-universal-homeomorphism-moduli-map).

The point quotient, smooth-atlas topology, 2-fibre product and its projection are the
existing constructions. Tests range over all algebraic stacks in the chosen size bound.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- A morphism is a universal homeomorphism when every algebraic-stack base change
induces a homeomorphism of the existing point spaces. Tests are not restricted to DM
stacks or representable morphisms. The common bound includes the scheme site.
Source: Stacks Project, Morphisms of Stacks, Tag 0CI7, definition-universal-homeomorphism
(blueprint: def-sfb-universal-homeomorphism-moduli-map). -/
def IsUniversalHomeomorphismModuliMap {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (Z : BasedCategory.{max u v₁ v₂, max (u + 1) w₁ w₂} (Over S)),
    IsAlgebraicModuliStack Z → ∀ g : BasedFunctor Z G,
      IsHomeomorph (moduliPointMap (moduliTwoFiberFst g f))

end CategoryTheory
