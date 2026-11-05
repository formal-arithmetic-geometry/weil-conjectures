/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueFiniteReduction
public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueQuotientLift
public import WeilConjectures.AlgebraicGeometry.Residue.ResidueLissePerfectLift
import all WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueFiniteReduction
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import all WeilConjectures.AlgebraicGeometry.Residue.ResidueLissePerfectLift
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarCoefficientEquivalence

/-! # Constants under the normalized finite coefficient comparison

Source: Bhatt--Scholze, Lemma 6.5.8(1),(2) and Proposition 6.6.11.
(blueprint: lem-weil-pbc-integral-residue-finite-constants).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] constantPresentation constantPresentationRestriction
  associatedConstants constantScalarSquare derivedChangeIso restrictSquare

attribute [local irreducible] transportedPresentation liftedRestriction

attribute [local irreducible] ordinaryConstants

end AlgebraicGeometry.Scheme
