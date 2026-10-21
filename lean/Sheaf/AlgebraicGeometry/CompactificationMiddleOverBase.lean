/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.Compactification.BoundaryRefinement
public import WeilConjectures.Compactification.Over

/-!
# The middle scheme of a compactification over a base

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-def-sfb-dc-setting/_section.md, statement paragraph 3; Stacks Tags 01KU, 01T3 and 01K4
(blueprint: lem-sfb-compactification-middle-over-base).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Compactification

/-- A given compactification of a morphism over a qcqs base has a unique compatible
structure morphism, namely its proper map followed by the target structure morphism.
Its middle scheme is separated and of finite type over the base and is quasi-compact.
The canonical arrows in the slice category retain the original underlying maps.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-def-sfb-dc-setting/_section.md, statement paragraph 3; Stacks Tags 01KU, 01T3 and 01K4
(blueprint: lem-sfb-compactification-middle-over-base).

Proof:
1. Set `aZ = c.obj.obj.g ≫ Y.hom`, the structure map of `c.obj.obj.overObj`.
The proper arrow is over the base by construction. Associativity, `c.obj.obj.comm`,
and `Over.w f` give `c.obj.obj.i ≫ aZ = X.hom`. Conversely, compatibility of the
proper arrow forces every structure morphism to equal `aZ`. The existing
`overI` and `overG` have underlying arrows `i` and `g`; their composite equals `f`
by equality of underlying arrows. This uses `def-weil-scheme-over-base` and
`sk-def-nagata-sketch-data`.
2. Properness of `c.obj.obj.g` gives separatedness and finite type
(`def-weil-proper-morphism`); it imposes no hypothesis on the source structure map.
3. Compose separated morphisms using clause (e) of
`lem-weil-pbc-proper-fp-permanence` (Stacks Tag 01KU) to get separatedness of `aZ`.
4. Compose finite-type morphisms using clause (1) of
`lem-sfb-finite-type-composition-base-change` (Stacks Tag 01T3) to get finite type of `aZ`.
5. Finite type includes quasi-compactness (`def-weil-finite-type-morphism`).
Clause (2) of `lem-weil-pbc-qcqs-morphism-permanence` (Stacks Tag 01K4) then gives
quasi-compactness of the middle scheme since the base is quasi-compact.
The open immersion remains quasi-compact by the supplied compactification datum.
No existence or choice of a compactification is used. -/
theorem compactification_middle_over_base {S : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] {X Y : Over S} (f : X ⟶ Y)
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (c : BoundaryCompactification f.left) :
    (∃! aZ : c.obj.obj.Z ⟶ S,
      c.obj.obj.i ≫ aZ = X.hom ∧ c.obj.obj.g ≫ Y.hom = aZ) ∧
    IsSeparated c.obj.obj.overObj.hom ∧
    LocallyOfFiniteType c.obj.obj.overObj.hom ∧
    QuasiCompact c.obj.obj.overObj.hom ∧
    CompactSpace c.obj.obj.Z ∧
    c.obj.obj.overI ≫ c.obj.obj.overG = f ∧
    IsOpenImmersion c.obj.obj.overI.left ∧
    QuasiCompact c.obj.obj.overI.left ∧
    IsProper c.obj.obj.overG.left := by
  sorry

end AlgebraicGeometry.Compactification
