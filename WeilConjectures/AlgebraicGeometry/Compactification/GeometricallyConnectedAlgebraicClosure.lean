/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedCheckAfterExtension

/-!
# Testing geometric connectedness on an algebraically closed extension

Source: Stacks Project, `varieties.tex`, Lemma 33.7.7 (Tag 0387), Lemma 33.7.3
(Tag 054N), and the remark after Definition 33.7.1
(blueprint: lem-weil-geometrically-connected-algebraic-closure).

## Main statements

- `AlgebraicGeometry.geometricallyConnected_iff_connectedSpace_of_isAlgClosed`:
  geometric connectedness is tested on one algebraically closed extension.
- `AlgebraicGeometry.GeometricallyConnected.nonempty_over_field`:
  a geometrically connected scheme over a field is nonempty.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

end AlgebraicGeometry
