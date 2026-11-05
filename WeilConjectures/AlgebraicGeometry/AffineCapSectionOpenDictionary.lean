/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.RingTheory.AffineFiniteProjectivePrimeMembership
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Ideal.Maps
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Affine dictionary for an invertible module and its section

Source: literature/stacks-project/schemes.tex, Schemes, Lemmas 01IA and 01IB,
together with Modules, Lemma 01CY (blueprint: lem-sc-affine-cap-section-open-dictionary).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.QuasicoherentTilde

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
