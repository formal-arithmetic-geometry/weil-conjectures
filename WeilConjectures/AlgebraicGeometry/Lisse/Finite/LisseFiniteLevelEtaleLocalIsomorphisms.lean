/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerEtaleDescentData
import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteLevelProEtaleLocalIsoSections
import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteLevelEtaleLocalRepresentative

/-! # Local isomorphism representatives for a finite-level model

Source: Stacks Project, proetale.tex, Tags 099Y, 099Z, 09B1 and 09BV.
(blueprint: lem-weil-pbc-lisse-finite-level-etale-local-isomorphisms).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow lisseTowerFixedRealization

end AlgebraicGeometry.Scheme
