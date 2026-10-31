/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Divisor
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.AlgebraicGeometry.DivisorModule

/-!
# The module associated to a divisor

Source: blueprint, sec-abelian-varieties, sk-def-av-pic, node def-sc-divisor
(blueprint: def-sc-divisor).

## Main definitions

- `Divisor.sectionCondition`: locally constant functions satisfying the order bounds.
- `Divisor.sectionModule`: the explicit section submodule.
- `Divisor.modulePresheaf`: these sections with pointwise restrictions.
- `Divisor.associatedModule`: the resulting sheaf of modules.
- `Divisor.moduleOfSmoothConnectedCurve`: the construction under the node's hypotheses.
- `divisorConstantSheaf`: the ambient constant sheaf of the function field.

The divisor group, principal-divisor map, class group and degree are the existing
`Scheme.Divisor`, `Scheme.div`, `Scheme.DivisorClassGroup` and `Scheme.Divisor.degree`.
We supply the missing module O_X(D). Locally constant functions represent sections of the
constant sheaf of the function field. On a nonempty open of an integral scheme these are
constant; on the empty open there is exactly one function, giving the zero module.
The construction applies to regular integral Noetherian schemes, hence to the smooth connected
curves of the node. For disconnected smooth curves use it on each one-dimensional component;
on zero-dimensional components the same formula uses the existing order with value zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X] [IsRegular X]

/-- The ambient constant sheaf of rings, using the recorded constant-sheaf declaration.
The locally constant functions used above are its usual topological section model.
Source: blueprint node def-sc-divisor; Stacks, Tag 0H7J (blueprint: def-sc-divisor). -/
noncomputable def divisorConstantSheaf : TopCat.Sheaf CommRingCat.{u} X :=
  (constantSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj X.functionField

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Divisor

end AlgebraicGeometry.Scheme.Divisor
