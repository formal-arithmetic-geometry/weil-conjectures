/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.AlgebraicGeometry.GlobalHomPullbackComparison

/-! # Canonical pullback comparison on global derived Hom

Compatibility import for the adopted canonical construction. Keeping a second copy
of the public declarations prevents importing the mixed-universe transport theorem.
The private equality in GlobalHomBaseChangeCounitTransport checks that the former
evaluation-mate expression agrees with the adopted construction, including its
tensorator and Leray comparison.

Source: Stacks Project, Tags 08I3, 0B6A and 0AA8.
(blueprint: def-pc-global-hom-pullback-comparison).
-/

@[expose] public section
