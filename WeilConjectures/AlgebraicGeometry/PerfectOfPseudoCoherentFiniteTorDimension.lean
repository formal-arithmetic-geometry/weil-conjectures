/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.FiniteTorDimension
import WeilConjectures.AlgebraicGeometry.AffineSheafificationTorAmplitude
import WeilConjectures.AlgebraicGeometry.AffineLocalizedDerivedSheafification
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.Finiteness.Projective
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect

/-! # Pseudo-coherent complexes of finite Tor dimension are perfect

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.49.5, Tag 08CQ
(blueprint: lem-pc-pseudo-coherent-finite-tor-perfect).
-/

@[expose] public section

universe uP wP

open CategoryTheory

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
