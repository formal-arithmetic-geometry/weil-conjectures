/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Scalar compatibility from a resolution counit

Source: Stacks Project, Tag 06Y6, lemma-derived-base-change
(blueprint: lem-pc-base-derived-extension-scalar).
-/

@[expose] public section

set_option autoImplicit false

universe uR uB v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

variable (R : Type uR) (B : Type uB) [CommRing R] [CommRing B]
  [Algebra R B]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uB v} R)]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uB v} B)]

end ModuleCat
