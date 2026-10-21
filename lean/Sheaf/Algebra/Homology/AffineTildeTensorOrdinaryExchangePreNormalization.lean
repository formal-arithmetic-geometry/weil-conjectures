/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison
public import Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative
public import WeilConjectures.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalization

/-! # Derived affine exchange before target reassociation

Compatibility interface for the complete adopted source implementation.
The derived affine exchange equation is re-exported under its original name.
The source proof localizes the ordinary chain equality and applies naturality
of the right-derived pushforward unit, without assuming the pullback counit
is invertible.

Source: Stacks Project, Tags 06Y6 and 08HY.
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange-prenormalization).
-/

@[expose] public section
