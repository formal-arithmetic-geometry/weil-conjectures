/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueQuotient
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.PrimitiveRootsCover
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.Mathlib.LinearAlgebra.Lagrange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Compatible primitive roots on one pro-étale cover

Source: clause 1 of the local-freeness statement in the current blueprint Tate-twist unit.
(blueprint: lem-poincare-compatible-primitive-roots)
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite Polynomial
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
open Scheme

end AlgebraicGeometry.ProEtale
