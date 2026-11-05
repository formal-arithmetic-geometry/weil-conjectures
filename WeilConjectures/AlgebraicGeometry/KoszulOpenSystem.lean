/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Single

/-! # The truncated Koszul system on a finite principal open

Source: Stacks Project, Tags 08CX and 08DC (blueprint: def-sc-koszul-open-system).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

variable (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)

variable [HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]

end
end AlgebraicGeometry
