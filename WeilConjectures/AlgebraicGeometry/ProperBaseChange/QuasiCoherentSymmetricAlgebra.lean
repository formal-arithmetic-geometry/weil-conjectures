/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebraCore
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebraAffine

/-! # The symmetric algebra of a quasi-coherent module

Source: Stacks Project, Modules, Section 01CF and Lemmas 01CG, 01CL; Schemes,
Section 01LA (9) (blueprint: lem-weil-pbc-quasi-coherent-symmetric-algebra).

The algebra is a commutative ring sheaf under the structure sheaf. The affine comparison
is a ring equivalence commuting with the structure homomorphism and the degree-one map;
this is precisely the canonical algebra isomorphism, without choosing algebra instances.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

end AlgebraicGeometry
