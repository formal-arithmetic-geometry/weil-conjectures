/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerPulledScalar
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.CoefficientSheafificationSquare.CoefficientSheafificationIso
import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf

/-! # Constant models for localized fixed realization

Source: Stacks Project, Modules on Sites, Tags 03CY and 03DA; Sites, Tag 0H7J;
Cohomology on Sites, Tag 06YY.

This is the model-existence part of
`lem-weil-pbc-lisse-tower-localized-constants`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow lisseTowerAlgebraArrow

/- Constant module presheaves are left adjoint to evaluation at a terminal object. -/

/- Sheafifying first in fixed coefficients gives the same module presentation. -/

/- Compare left adjoints using global sections with their actual scalar actions. -/

/- Changing an isomorphic ring presentation commutes with module sheafification. -/

/- The chosen finite coefficient isomorphism respects the constant-ring units. -/

/- Assemble the constant model before passing to complexes and localization. -/

end AlgebraicGeometry.Scheme
