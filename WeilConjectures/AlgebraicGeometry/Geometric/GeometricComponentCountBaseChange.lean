/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.SetTheory.Cardinal.Finite

import WeilConjectures.FieldTheory.CommonExtensionFields
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SepClosedFieldComponentsBijection

/-!
# Geometric component counts and base change

Source: Stacks Project, More on Morphisms, Tag 055F,
`lemma-base-change-fibres-nr-geometrically-connected-components`
(blueprint: lem-weil-pbc-geometric-component-count-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

end AlgebraicGeometry
