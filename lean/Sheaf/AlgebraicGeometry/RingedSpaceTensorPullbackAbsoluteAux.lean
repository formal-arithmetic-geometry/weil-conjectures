/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackAbsoluteAux

/-!
# Compatibility import for absolute tensor pullback

The adopted source library supplies `exists_tensorPullback_leftDerived` and
`leftDerived_tensorPullback_absolute`, with their K-flat resolving-class proofs.
Re-export that implementation so that existing imports use a single declaration of
both the tensor pullback construction and its derived comparison.
-/
