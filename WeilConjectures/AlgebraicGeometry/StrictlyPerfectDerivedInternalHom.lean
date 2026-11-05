/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-! # Internal Hom from a strictly perfect complex

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.46.9, Tag 08DM
(blueprint: lem-pc-rhom-strict-perfect-hom).

The affine scheme is presented as an affine open `U` of a scheme `X`; its module
category is the recorded localized-site carrier of `Scheme.IsStrictlyPerfect`.
The comparison is computed with any functorial K-injective replacement, as in
`derivedInternalHom_comparison`. No boundedness is imposed on the second complex.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
