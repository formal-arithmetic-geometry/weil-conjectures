/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparisonSupplement
public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeRepresentativeSupplement
public import WeilConjectures.Algebra.Homology.AffineTildeTensorOrdinaryExchange

/-! # Ordinary affine exchange in tensor coordinates

Compatibility interface for the complete adopted source implementation.
The coefficient target map and its ordinary exchange equation are re-exported
under their original fully qualified names. The legacy `affineTildeFunctor`
is an abbreviation of the associated-sheaf functor used by that implementation.

Source: Stacks Project, Tags 01I9, 06Y6 and 08HY.
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange).
-/

@[expose] public section
