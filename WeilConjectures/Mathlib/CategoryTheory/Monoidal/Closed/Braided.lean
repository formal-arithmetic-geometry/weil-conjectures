/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Tensoring on the right with a closed object preserves colimits

In a braided monoidal category, if `A` is a closed object, then `tensorRight A`
preserves colimits: it is isomorphic to `tensorLeft A` via the braiding, and
`tensorLeft A` is a left adjoint. This complements the instance
`ihom.instIsLeftAdjointTensorRight` of `Mathlib.CategoryTheory.Monoidal.Closed.Braided`
and the instance `PreservesColimits (tensorLeft A)` of
`Mathlib.CategoryTheory.Monoidal.Closed.Basic`.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.ihom

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]

instance (A : C) [Closed A] : PreservesColimits (tensorRight A) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight A)

end CategoryTheory.ihom
