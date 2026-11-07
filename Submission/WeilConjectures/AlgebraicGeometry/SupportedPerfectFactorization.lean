/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated
import Submission.WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import all Submission.WeilConjectures.CategoryTheory.CompactGeneratorAmbientThick
import all Submission.WeilConjectures.AlgebraicGeometry.DerivedQCohCompactRepresentatives
import all Submission.WeilConjectures.AlgebraicGeometry.SupportedKoszulRelativeDetector

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Perfect factorization of maps to supported complexes

Source: Stacks Project, Tags 0A9C, 0E4G, 094A and 09SP.
(blueprint: lem-sc-supported-perfect-factorization).
-/
