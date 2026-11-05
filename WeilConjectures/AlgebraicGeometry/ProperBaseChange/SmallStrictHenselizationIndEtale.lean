/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.RingTheory.ProEtale.IndEtale
import WeilConjectures.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale

/-! # Ind-etaleness for the small representative strict henselization

Transport the upstream affine-chart theorem along the canonical comparison of the small
representative colimit with the full affine pointed-neighbourhood colimit.
Source: Stacks Project, Tags 04HX and 04GW.
(blueprint: lem-weil-pbc-small-strict-henselization-ind-etale).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
