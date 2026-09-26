/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Kernels of morphisms of group objects

In a cartesian monoidal category with pullbacks, the kernel of a morphism `f : G ⟶ H` of
group objects is the fibre product of `f` and the unit `η[H] : 𝟙_ C ⟶ H`.

## Main definitions

- `CategoryTheory.GrpObj.ker`: the kernel of a morphism of group objects.
-/

@[expose] public section

namespace CategoryTheory

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

namespace GrpObj

variable {G H : C} [GrpObj G] [GrpObj H]

/-- Blueprint `sk-def-av-group-scheme`: Group schemes, order, and étaleness.

The kernel of a morphism `f : G ⟶ H` of group objects: the fibre product of `f` with the unit
`η[H] : 𝟙_ C ⟶ H`. For group schemes over a field this is the kernel subgroup scheme. -/
noncomputable def ker (f : G ⟶ H) [HasPullback f η[H]] : C := pullback f η[H]

/-- The canonical morphism from the kernel of `f : G ⟶ H` to `G`. -/
noncomputable def kerι (f : G ⟶ H) [HasPullback f η[H]] : ker f ⟶ G := pullback.fst _ _

end GrpObj

end CategoryTheory
