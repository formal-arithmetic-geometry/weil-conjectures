/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement

/-!
# Ordinary pro-etale operations with arbitrary constant coefficients

Source: Stacks Project, Modules on Sites, lemma-adjoint-push-pull-modules, and Tag 0H7J
(blueprint: def-weil-pbc-proetale-operations).

This supplies the arbitrary-constant-ring specialization of the published ring-sheaf
operations. The intrinsic finite-coefficient interface remains available.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [instance] proEtaleConstantRingComparison_isIso

end AlgebraicGeometry.Scheme
