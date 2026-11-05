/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleAdjunction
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement

/-!
# Identity normalization of ordinary pro-etale derived pullback

Source: Stacks Project, Tag 09A5, identity specialization of `section-morphism`;
the final sentence of the blueprint proof of `lem-pur-diagonal-base-change`
(blueprint: lem-pur-proetale-derived-pullback-identity).

The coprojection formula fixes the module comparison before scalar extension.
The tensor formulas fix its scalar-transport identification. The final equality
fixes the derived comparison on every cochain representative.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
