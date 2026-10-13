/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# A sheaf with vanishing stalks is zero

Source: upstream review #1428, recorded in coord/upstream-review-20261013.md.
(blueprint: pqf-lem-sheaf-zero-stalks)

The upstream module `WeilConjectures.AlgebraicGeometry.Cohomology.FiniteFibre` now
provides `AlgebraicGeometry.Scheme.Modules.isZero_of_isZero_stalk`. The former
`isZero_of_isZero_stalks` declaration was a duplicate and has been retired.
No local declaration callers need adaptation.

This compatibility module intentionally contains no declarations after duplicate removal.
-/

@[expose] public section
