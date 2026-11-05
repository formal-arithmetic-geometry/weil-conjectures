/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.CategoryTheory.Sites.LeftExact

/-! # Construction of the symmetric algebra sheaf

Source: Stacks Project, Modules, Lemma 01CG (lemma-local-tensor-algebra).
(blueprint: lem-weil-pbc-symmetric-algebra-sheaf-construction).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory Opposite TopologicalSpace
namespace AlgebraicGeometry.SymmetricAlgebraSheaf
variable {X : Scheme.{u}} (F : X.Modules)

end AlgebraicGeometry.SymmetricAlgebraSheaf
