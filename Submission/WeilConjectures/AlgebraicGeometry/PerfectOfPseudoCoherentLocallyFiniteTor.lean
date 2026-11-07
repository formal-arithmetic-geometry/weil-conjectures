/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import Submission.WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Submission.WeilConjectures.AlgebraicGeometry.LocallyFiniteTorDimension
import Submission.WeilConjectures.AlgebraicGeometry.AffineLocalSheafificationTorAmplitude
import Submission.WeilConjectures.AlgebraicGeometry.AffineLocalizedDerivedSheafification
import all Submission.WeilConjectures.AlgebraicGeometry.PerfectOfPseudoCoherentFiniteTorDimension
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Pseudo-coherent complexes of locally finite Tor dimension are perfect

Source: Stacks Project, Cohomology of Sheaves, Tag 08CQ, implication (2) to (1).
(blueprint: lem-pc-pseudo-coherent-locally-finite-tor-perfect).
-/

@[expose] public section

universe uP wP

open CategoryTheory

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
