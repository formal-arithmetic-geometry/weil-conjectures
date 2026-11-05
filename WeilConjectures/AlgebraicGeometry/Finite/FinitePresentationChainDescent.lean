/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.Finite.FinitePresentationFamilyDescent
import WeilConjectures.AlgebraicGeometry.Finite.FinitePresentationArrowsDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.Curve.GenericModelAux
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.DescendSurjective
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.EventuallyProper
import WeilConjectures.AlgebraicGeometry.IsOpenImmersion.OpenImmersionInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.DescendSmoothQcqs
import Mathlib.Order.Filter.AtTopBot.Finite

/-!
# Common-stage descent of finite chains with a finite comparison

Source: Stacks Project, Limits, Tags 01ZM, 01ZO, 07RR, 07RP, 0EUU, 0C0C and 081F.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

end AlgebraicGeometry
