/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraSheafConstruction
public import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion

/-! # The tilde comparison for the symmetric algebra on an affine open

Source: Stacks Project, Schemes, Lemma 01I7 and Modules, Lemma 01CG.
(blueprint: def-weil-pbc-symmetric-algebra-affine-comparison-map).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.SymmetricAlgebraSheaf

variable {X : Scheme.{u}}

end AlgebraicGeometry.SymmetricAlgebraSheaf
