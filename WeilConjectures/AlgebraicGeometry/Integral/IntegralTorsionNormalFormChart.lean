/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import WeilConjectures.Mathlib.Algebra.Module.PID
import WeilConjectures.AlgebraicGeometry.Integral.IntegralConstantFreeChart
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTorsionTorTransport
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTorsionTorConstant

/-!
# Torsion normal form on a perfect chart

On a chart where a complete integral complex is the completed realization of a perfect
complex over the valuation ring, its cohomology splits as a finite free sheaf and a
nilpotent-uniformizer torsion sheaf, and the cokernel of the uniformizer on the torsion
part is a quotient of the consecutive-quotient Tor sheaf.

Source: Bhatt--Scholze, Proposition 6.6.11; the elementary-divisor calculation in step 5
of `lem-weil-pbc-adic-tor-implies-flat-cohomology`
(blueprint: lem-weil-pbc-integral-cohomology-torsion-normal-form).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

section Helpers

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

variable {l E}

end Helpers

end AlgebraicGeometry.Scheme
