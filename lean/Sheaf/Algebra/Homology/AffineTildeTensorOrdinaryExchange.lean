/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison
public import Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative
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
