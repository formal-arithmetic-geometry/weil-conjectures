/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackPointTopology

/-! # Universal homeomorphisms of algebraic stacks

Source: Stacks Project, stacks-morphisms.tex, definition-universal-homeomorphism
(blueprint: def-sfb-stack-universal-homeomorphism).

The property uses the canonical projection of the existing 2-fibre product and the
existing smooth-atlas topology. No representability condition is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open AlgebraicGeometry

namespace CategoryTheory

/-- A universal homeomorphism induces a homeomorphism on point spaces after every
algebraic-stack base change. The test universe includes the base site and both endpoints,
and has independently variable additional bounds `v₃` and `w₃`.
Source: Stacks Project, stacks-morphisms.tex, definition-universal-homeomorphism
(blueprint: def-sfb-stack-universal-homeomorphism). -/
def IsUniversalHomeomorphismAlgebraicModuliMap {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (Z : BasedCategory.{max u v₁ v₂ v₃, max (u + 1) w₁ w₂ w₃} (Over S))
      (g : BasedFunctor Z G),
    IsAlgebraicModuliStack Z → IsHomeomorph (moduliPointMap (moduliTwoFiberFst g f))

end CategoryTheory
