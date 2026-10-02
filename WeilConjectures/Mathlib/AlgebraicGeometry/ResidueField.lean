/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The geometric point over a point of a scheme

For a point `y` of a scheme `Y`, `Scheme.fromSpecResidueField` is the canonical morphism
`Spec κ(y) ⟶ Y`. This file names its composite with `Spec κ(y)‾ ⟶ Spec κ(y)`, where `κ(y)‾` is
the algebraic closure of `κ(y)`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The geometric point `Spec κ(y)‾ ⟶ Y` over a point `y` of a scheme `Y`, where `κ(y)‾` is the
algebraic closure of the residue field `κ(y)`. It is the composite

```
  Spec κ(y)‾ ──▶ Spec κ(y) ── fromSpecResidueField y ──▶ Y
```
-/
noncomputable def fromSpecAlgebraicClosureResidueField (Y : Scheme.{u}) (y : Y) :
    Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure _))) ≫
    Y.fromSpecResidueField y

end AlgebraicGeometry.Scheme
