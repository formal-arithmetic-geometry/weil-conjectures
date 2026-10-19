/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite

/-!
# Retired duplicate (2026-10-17)

The source library proves blueprint node
`thm-pqf-finite-iff-proper-finite-fibres`
sorry-free as
`AlgebraicGeometry.IsFinite.iff_isProper_and_finite_preimage_singleton`
in
`WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite`
This module re-exports it. Its sorried declaration
`AlgebraicGeometry.isFinite_iff_isProper_and_hasFiniteFibres`
is gone (no module used it).
-/
