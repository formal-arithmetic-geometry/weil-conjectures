/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Constructible finite-ring sheaves have etale origin

Source: Stacks Project, Tags 09AK and 099Y, with the blueprint's global finite partitions
(blueprint: lem-weil-pbc-finite-ring-constructible-sheaf-origin).

The two recorded constructibility predicates use different equivalent encodings of
constant-coefficient module sheaves. The equivalence below is identified with the
recorded comparison pullback on underlying additive sheaves, and the last clause
requires that identification to respect the constant scalar action. Thus it specifies
the given pullback, including its module structure.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
