/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulSite
import WeilConjectures.AlgebraicGeometry.Weil.WeilExteriorKoszulTensorComparison
import WeilConjectures.AlgebraicGeometry.Weil.WeilNegativeKoszulTensorDualTransport

/-! # The finite coefficient comparison, before tensoring with an input complex

Source: Stacks Project, algebraization.tex, Tag 0A0E, with Modules on Sites, Tags 03DA and 03EK.
(blueprint: lem-weil-pbc-completed-koszul-coefficient-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
