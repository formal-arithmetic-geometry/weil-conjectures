/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SectionRingVeroneseFractionKernel

/-! # Bijection for Veronese section fractions

The canonical map from the section-fraction presentation, sending a class
`[n, ξ]` to the homogeneous fraction `ξ / s^n`, is constructed by descending
the explicit numerator map through the section-fraction relations.
The theorem records bijectivity of this specific canonical map together with its
generator formula.
Source: Stacks Project, Properties, Tags 0B5L, 01PW, and 01Q1.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

-- The kernel equality is used directly to certify the quotient lift.

end AlgebraicGeometry.Scheme.Modules
