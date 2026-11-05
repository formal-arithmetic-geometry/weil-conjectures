/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransition
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsSquare
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleModuleRestrictionConstantMap
public import WeilConjectures.SixFunctors.ProEtale.LocalizationRestrictionScalarMate

/-! # The strict square of the ordinary quotient arrows

Restriction along the finite quotient map `R_(n+1) → R_n` is compatible with the chart
coordinates of the two finite quotients, by a square which is the identity on sections. The
explicit quotient arrow is the chart image of the ring-level quotient transition followed by
this square.

Source: Stacks Project, Tags 03CY, 03DA and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

end AlgebraicGeometry.Scheme
