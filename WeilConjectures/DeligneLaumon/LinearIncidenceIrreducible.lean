/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Topology.Irreducible

import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Irreducibility of an affine linear incidence hypersurface

Source: Stacks Project, `more-morphisms.tex`, Tag 0G4F, lemma `lemma-bertini-irreducible`,
middle proof paragraph (blueprint: lem-zl-linear-incidence-irreducible).
-/

@[expose] public section

universe u v

open AlgebraicGeometry

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

end
