/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicFiniteDiagramData
public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRealizationDataSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantModuleModel
import all WeilConjectures.AlgebraicGeometry.Relative.RelativeCompletedModuleRealizationExact
import all WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicLisseRelativeRestriction
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcFinitePullbackConstructibility
import WeilConjectures.AlgebraicGeometry.Relative.RelativeFiniteCoefficientTransport

/-! # Scalar factorization of the relative completed constant realization

Source: Stacks Tags 06YY, 06YU and 0D6D; flat completion (Tag 093M).
(blueprint: lem-weil-pbc-completed-constant-derived-scalar-factorization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
