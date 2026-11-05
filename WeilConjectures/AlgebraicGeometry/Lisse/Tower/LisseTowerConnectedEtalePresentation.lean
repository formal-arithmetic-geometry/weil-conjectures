/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Noetherian

import all WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteQuotientEtaleOrigin
import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientModelReduction
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingDerivedLocalConstancy
import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-! # Connected etale presentations before choosing local stalk markings

Source: Stacks Project, proetale.tex, Tags 09AL, 09B1 and 09C6.
(blueprint: lem-weil-pbc-lisse-tower-connected-etale-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local irreducible] constantAdicQuotientRealization

end AlgebraicGeometry.Scheme
