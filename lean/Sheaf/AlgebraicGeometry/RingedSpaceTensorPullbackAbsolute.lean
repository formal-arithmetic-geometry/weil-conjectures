/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute

/-!
# Compatibility import for absolute left derived tensor pullback

The adopted source library proves `exists_absolute_leftDerived_tensorModulePullback`
from the K-flat derived comparison and its absoluteness under postcomposition.
Re-export that implementation to preserve the existing import path without a second
declaration of the same theorem.

Source: Stacks Project, Cohomology, Tags 06YJ and 079W; Derived Categories, Tag 06XN.
(blueprint: lem-pc-ringed-space-tensor-pullback-absolute)
-/

@[expose] public section
