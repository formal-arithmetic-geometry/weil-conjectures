/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulSite
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedModuleTensorTransport
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! # The tensor comparison for completed coefficient and site transport

Source: Stacks Project, algebraization.tex, Tag 0A0E, with Modules on Sites, Tags 03DA and 03EK.
(blueprint: lem-weil-pbc-completed-cech-tensor-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

open MonoidalCategory

attribute [local irreducible] completedCechModulesEquiv intrinsicPresentationRoundTrip
  pbcCompletedComparison

end AlgebraicGeometry.Scheme
