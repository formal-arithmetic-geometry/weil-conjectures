/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Extending constant coefficients to the constant ring sheaf

Source: Stacks Project, Modules on Sites, Sections 093I and 03CV;
Sites Example 0H7J.
(blueprint: lem-weil-pbc-etale-constant-ring-module-equivalence)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Functor

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]

end AlgebraicGeometry.Scheme
