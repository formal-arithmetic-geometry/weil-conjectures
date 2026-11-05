/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeExtensionCohomologyNormalization
import WeilConjectures.AlgebraicGeometry.Cartier.CartierPairPullbackSection
import all WeilConjectures.AlgebraicGeometry.Relative.RelativeFramedExtensionPullback
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierPairTensorAddition
import all WeilConjectures.AlgebraicGeometry.CartierComplementFrame
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import all WeilConjectures.AlgebraicGeometry.Modules.SectionAvoidance
import all WeilConjectures.AlgebraicGeometry.InternalHomRestrictScheme

/-!
# Pullback of the integral Cartier pole extension

Source: blueprint lem-amb-cartier-kummer-map, relative trivialization paragraph;
Stacks 03AJ and 0A45 (blueprint: lem-asd-cartier-pole-boundary-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Scheme.Modules.framePullbackMap

end AlgebraicGeometry.Etale
