/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraSheafConstruction

/-! # Core universal property for the symmetric algebra sheaf

Source: Stacks Project, Modules, Lemmas 01CG and 01CL.
(blueprint: lem-weil-pbc-quasi-coherent-symmetric-algebra-core).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry

namespace SymmetricAlgebraSheaf

variable {X : Scheme.{u}} (F : X.Modules) (B : X.CommAlgebraSheaf)
  (f : F ⟶ B.toModule)

end SymmetricAlgebraSheaf

end AlgebraicGeometry
